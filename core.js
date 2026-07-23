// ============================================================
// RV32 Workbench core: C-subset compiler -> RV32IM asm -> machine code -> CPU
// ============================================================

// ---------------- Tokenizer ----------------
const KEYWORDS = new Set(['int','char','void','if','else','while','for','return','break','continue','sizeof']);
const PUNCTS = ['<<=','>>=','==','!=','<=','>=','&&','||','<<','>>','+=','-=','*=','/=','%=','&=','|=','^=','++','--',
  '+','-','*','/','%','&','|','^','~','!','<','>','=','(',')','{','}','[',']',',',';','?',':'];

function CErr(msg, line){ const e = new Error(msg); e.cline = line; e.isCompile = true; return e; }

function tokenize(src){
  const toks = []; let i = 0, line = 1;
  const n = src.length;
  function esc(c){ return {n:'\n',t:'\t',r:'\r','0':'\0','\\':'\\','\'':'\'','"':'"'}[c] !== undefined ? {n:'\n',t:'\t',r:'\r','0':'\0','\\':'\\','\'':'\'','"':'"'}[c] : c; }
  while (i < n){
    const c = src[i];
    if (c === '\n'){ line++; i++; continue; }
    if (c === ' ' || c === '\t' || c === '\r'){ i++; continue; }
    if (c === '/' && src[i+1] === '/'){ while (i < n && src[i] !== '\n') i++; continue; }
    if (c === '/' && src[i+1] === '*'){
      i += 2;
      while (i < n && !(src[i] === '*' && src[i+1] === '/')){ if (src[i] === '\n') line++; i++; }
      if (i >= n) throw CErr('unterminated comment', line);
      i += 2; continue;
    }
    if (/[0-9]/.test(c)){
      let j = i;
      if (c === '0' && (src[i+1] === 'x' || src[i+1] === 'X')){
        j = i + 2; while (j < n && /[0-9a-fA-F]/.test(src[j])) j++;
        toks.push({type:'num', val: parseInt(src.slice(i, j), 16) | 0, line});
      } else {
        while (j < n && /[0-9]/.test(src[j])) j++;
        toks.push({type:'num', val: parseInt(src.slice(i, j), 10) | 0, line});
      }
      i = j; continue;
    }
    if (/[A-Za-z_]/.test(c)){
      let j = i; while (j < n && /[A-Za-z0-9_]/.test(src[j])) j++;
      const w = src.slice(i, j);
      toks.push({type: KEYWORDS.has(w) ? 'kw' : 'ident', val: w, line});
      i = j; continue;
    }
    if (c === '\''){
      i++;
      let v;
      if (src[i] === '\\'){ v = esc(src[i+1]).charCodeAt(0); i += 2; }
      else { v = src.charCodeAt(i); i++; }
      if (src[i] !== '\'') throw CErr('unterminated char literal', line);
      i++;
      toks.push({type:'num', val: v, line}); continue;
    }
    if (c === '"'){
      i++;
      let s = '';
      while (i < n && src[i] !== '"'){
        if (src[i] === '\n') throw CErr('unterminated string', line);
        if (src[i] === '\\'){ s += esc(src[i+1]); i += 2; }
        else { s += src[i]; i++; }
      }
      if (i >= n) throw CErr('unterminated string', line);
      i++;
      toks.push({type:'str', val: s, line}); continue;
    }
    let matched = null;
    for (const p of PUNCTS){ if (src.startsWith(p, i)){ matched = p; break; } }
    if (!matched) throw CErr(`stray character '${c}'`, line);
    toks.push({type:'punct', val: matched, line});
    i += matched.length;
  }
  toks.push({type:'eof', val:'', line});
  return toks;
}

// ---------------- Types ----------------
const T_INT  = {kind:'int'};
const T_CHAR = {kind:'char'};
const T_VOID = {kind:'void'};
function ptrTo(b){ return {kind:'ptr', base: b}; }
function arrOf(b, len){ return {kind:'array', base: b, len}; }
function sizeOf(t){
  if (t.kind === 'int' || t.kind === 'ptr') return 4;
  if (t.kind === 'char') return 1;
  if (t.kind === 'array') return sizeOf(t.base) * t.len;
  return 0;
}
function isPtrLike(t){ return t.kind === 'ptr' || t.kind === 'array'; }
function baseOf(t){ return t.base; }
function isInteger(t){ return t.kind === 'int' || t.kind === 'char'; }

// Builtins handled as ecall sequences (RARS-style service codes)
const BUILTINS = {
  print_int:  {svc: 1,  args: 1, ret: T_VOID},
  print_str:  {svc: 4,  args: 1, ret: T_VOID},
  read_int:   {svc: 5,  args: 0, ret: T_INT},
  print_char: {svc: 11, args: 1, ret: T_VOID},
  exit:       {svc: 93, args: 1, ret: T_VOID},
};

// ---------------- Parser ----------------
function parse(toks){
  let pos = 0;
  const prog = {funcs: [], globals: [], strings: []};
  const globalMap = new Map();
  const funcMap = new Map();
  let curFn = null;
  let scopes = [];

  const peek = (k = 0) => toks[pos + k];
  const tok  = () => toks[pos];
  function next(){ return toks[pos++]; }
  function isP(v){ const t = tok(); return t.type === 'punct' && t.val === v; }
  function isKw(v){ const t = tok(); return t.type === 'kw' && t.val === v; }
  function eatP(v){ if (!isP(v)) throw CErr(`expected '${v}' but got '${tok().val || 'end of file'}'`, tok().line); pos++; }
  function eatKw(v){ if (!isKw(v)) throw CErr(`expected '${v}'`, tok().line); pos++; }

  function isTypeStart(){ return isKw('int') || isKw('char') || isKw('void'); }
  function parseBaseType(){
    if (isKw('int')){ pos++; return T_INT; }
    if (isKw('char')){ pos++; return T_CHAR; }
    if (isKw('void')){ pos++; return T_VOID; }
    throw CErr('expected a type', tok().line);
  }
  function parseStars(t){ while (isP('*')){ pos++; t = ptrTo(t); } return t; }

  function findVar(name){
    for (let s = scopes.length - 1; s >= 0; s--){
      if (scopes[s].has(name)) return scopes[s].get(name);
    }
    if (globalMap.has(name)) return globalMap.get(name);
    return null;
  }

  function newLocal(name, type, line){
    if (scopes[scopes.length - 1].has(name)) throw CErr(`redeclaration of '${name}'`, line);
    const v = {name, type, isLocal: true, offset: 0};
    scopes[scopes.length - 1].set(name, v);
    curFn.locals.push(v);
    return v;
  }

  // ---- expressions ----
  function numNode(v, line){ return {kind:'num', val: v, type: T_INT, line}; }

  function primary(){
    const t = tok();
    if (t.type === 'num'){ pos++; return numNode(t.val, t.line); }
    if (t.type === 'str'){
      pos++;
      let idx = prog.strings.indexOf(t.val);
      if (idx < 0){ idx = prog.strings.length; prog.strings.push(t.val); }
      return {kind:'str', idx, type: ptrTo(T_CHAR), line: t.line};
    }
    if (isP('(')){ pos++; const e = expr(); eatP(')'); return e; }
    if (isKw('sizeof')){
      pos++;
      if (isP('(') && (peek(1).type === 'kw' && peek(1).val !== 'sizeof')){
        pos++; let ty = parseStars(parseBaseType()); eatP(')');
        return numNode(sizeOf(ty), t.line);
      }
      const e = unary();
      return numNode(sizeOf(e.type), t.line);
    }
    if (t.type === 'ident'){
      pos++;
      if (isP('(')){ // call
        pos++;
        const args = [];
        if (!isP(')')){
          args.push(assign());
          while (isP(',')){ pos++; args.push(assign()); }
        }
        eatP(')');
        const b = BUILTINS[t.val];
        if (b){
          if (args.length !== b.args) throw CErr(`${t.val}() takes ${b.args} argument(s)`, t.line);
          return {kind:'builtin', name: t.val, svc: b.svc, args, type: b.ret === T_VOID ? T_INT : b.ret, line: t.line};
        }
        if (args.length > 8) throw CErr('at most 8 arguments are supported', t.line);
        const f = funcMap.get(t.val);
        return {kind:'call', name: t.val, args, type: f ? f.retType : T_INT, line: t.line};
      }
      const v = findVar(t.val);
      if (!v) throw CErr(`'${t.val}' is not declared`, t.line);
      return {kind:'var', v, type: v.type, line: t.line};
    }
    throw CErr(`unexpected '${t.val || 'end of file'}'`, t.line);
  }

  function mkDeref(e, line){
    if (!isPtrLike(e.type)) throw CErr('cannot dereference a non-pointer', line);
    if (e.type.base.kind === 'void') throw CErr('cannot dereference void*', line);
    return {kind:'deref', e, type: e.type.base, line};
  }
  function mkAdd(l, r, line){ // handles pointer arithmetic typing; ptr goes left
    if (isPtrLike(l.type) && isPtrLike(r.type)) throw CErr('cannot add two pointers', line);
    if (isPtrLike(r.type)){ const t = l; l = r; r = t; }
    const type = isPtrLike(l.type) ? ptrTo(l.type.base) : T_INT;
    return {kind:'bin', op:'+', l, r, type, line};
  }
  function mkSub(l, r, line){
    let type = T_INT;
    if (isPtrLike(l.type) && isPtrLike(r.type)) type = T_INT;
    else if (isPtrLike(l.type)) type = ptrTo(l.type.base);
    else if (isPtrLike(r.type)) throw CErr('cannot subtract a pointer from an integer', line);
    return {kind:'bin', op:'-', l, r, type, line};
  }

  function postfix(){
    let e = primary();
    for (;;){
      if (isP('[')){
        const line = tok().line; pos++;
        const idx = expr(); eatP(']');
        e = mkDeref(mkAdd(e, idx, line), line);
      } else if (isP('++') || isP('--')){
        const op = tok().val; const line = tok().line; pos++;
        requireLvalue(e, line);
        e = {kind:'postincdec', op, e, type: isPtrLike(e.type) ? ptrTo(e.type.base) : T_INT, line};
      } else break;
    }
    return e;
  }

  function requireLvalue(e, line){
    if (e.kind !== 'var' && e.kind !== 'deref') throw CErr('expression is not assignable', line);
    if (e.type.kind === 'array') throw CErr('an array is not assignable', line);
  }

  function unary(){
    const t = tok();
    if (isP('-')){ pos++; const e = unary(); return {kind:'neg', e, type: T_INT, line: t.line}; }
    if (isP('!')){ pos++; const e = unary(); return {kind:'lognot', e, type: T_INT, line: t.line}; }
    if (isP('~')){ pos++; const e = unary(); return {kind:'bitnot', e, type: T_INT, line: t.line}; }
    if (isP('*')){ pos++; const e = unary(); return mkDeref(e, t.line); }
    if (isP('&')){
      pos++; const e = unary();
      if (e.kind !== 'var' && e.kind !== 'deref') throw CErr("cannot take the address of this expression", t.line);
      const base = e.type.kind === 'array' ? e.type.base : e.type;
      return {kind:'addr', e, type: ptrTo(base), line: t.line};
    }
    if (isP('++') || isP('--')){
      const op = tok().val; pos++; const e = unary();
      requireLvalue(e, t.line);
      return {kind:'preincdec', op, e, type: isPtrLike(e.type) ? ptrTo(e.type.base) : T_INT, line: t.line};
    }
    return postfix();
  }

  function binLevel(sub, ops){
    return function(){
      let l = sub();
      for (;;){
        const t = tok();
        if (t.type === 'punct' && ops.includes(t.val)){
          pos++;
          const r = sub();
          if (t.val === '+') l = mkAdd(l, r, t.line);
          else if (t.val === '-') l = mkSub(l, r, t.line);
          else l = {kind:'bin', op: t.val, l, r, type: T_INT, line: t.line};
        } else return l;
      }
    };
  }
  const mul    = binLevel(unary, ['*','/','%']);
  const addsub = binLevel(mul, ['+','-']);
  const shift  = binLevel(addsub, ['<<','>>']);
  const rel    = binLevel(shift, ['<','>','<=','>=']);
  const eq     = binLevel(rel, ['==','!=']);
  const band   = binLevel(eq, ['&']);
  const bxor   = binLevel(band, ['^']);
  const bor    = binLevel(bxor, ['|']);

  function logand(){
    let l = bor();
    while (isP('&&')){ const line = tok().line; pos++; l = {kind:'logand', l, r: bor(), type: T_INT, line}; }
    return l;
  }
  function logor(){
    let l = logand();
    while (isP('||')){ const line = tok().line; pos++; l = {kind:'logor', l, r: logand(), type: T_INT, line}; }
    return l;
  }
  function ternary(){
    const c = logor();
    if (isP('?')){
      const line = tok().line; pos++;
      const a = assign(); eatP(':');
      const b = ternary();
      return {kind:'cond', c, a, b, type: a.type, line};
    }
    return c;
  }
  function assign(){
    const l = ternary();
    const t = tok();
    if (t.type === 'punct' && ['=','+=','-=','*=','/=','%=','&=','|=','^=','<<=','>>='].includes(t.val)){
      pos++;
      requireLvalue(l, t.line);
      const r = assign();
      if (t.val === '=') return {kind:'assign', l, r, type: l.type, line: t.line};
      return {kind:'opassign', op: t.val.slice(0, -1), l, r, type: l.type, line: t.line};
    }
    return l;
  }
  function expr(){ return assign(); }

  // ---- statements ----
  function declStmt(){
    const line = tok().line;
    const base = parseBaseType();
    const items = [];
    for (;;){
      let ty = parseStars(base);
      const nameTok = next();
      if (nameTok.type !== 'ident') throw CErr('expected a variable name', nameTok.line);
      if (isP('[')){
        pos++;
        const lenTok = next();
        if (lenTok.type !== 'num' || lenTok.val <= 0) throw CErr('array length must be a positive constant', lenTok.line);
        eatP(']');
        ty = arrOf(ty, lenTok.val);
      }
      if (ty.kind === 'void') throw CErr('variables cannot have type void', nameTok.line);
      const v = newLocal(nameTok.val, ty, nameTok.line);
      let init = null;
      if (isP('=')){
        pos++;
        if (ty.kind === 'array') throw CErr('local array initialisers are not supported', nameTok.line);
        init = assign();
      }
      items.push({v, init, line: nameTok.line});
      if (isP(',')){ pos++; continue; }
      break;
    }
    eatP(';');
    return {kind:'decl', items, line};
  }

  function stmt(){
    const t = tok();
    if (isP('{')){
      pos++;
      scopes.push(new Map());
      const body = [];
      while (!isP('}')) body.push(stmt());
      pos++;
      scopes.pop();
      return {kind:'block', body, line: t.line};
    }
    if (isKw('if')){
      pos++; eatP('('); const c = expr(); eatP(')');
      const then = stmt();
      let els = null;
      if (isKw('else')){ pos++; els = stmt(); }
      return {kind:'if', c, then, els, line: t.line};
    }
    if (isKw('while')){
      pos++; eatP('('); const c = expr(); eatP(')');
      return {kind:'while', c, body: stmt(), line: t.line};
    }
    if (isKw('for')){
      pos++; eatP('(');
      scopes.push(new Map());
      let init = null, c = null, inc = null;
      if (!isP(';')) init = isTypeStart() ? declStmt() : (() => { const e = {kind:'exprstmt', e: expr(), line: t.line}; eatP(';'); return e; })();
      else pos++;
      if (!isP(';')) c = expr();
      eatP(';');
      if (!isP(')')) inc = expr();
      eatP(')');
      const body = stmt();
      scopes.pop();
      return {kind:'for', init, c, inc, body, line: t.line};
    }
    if (isKw('return')){
      pos++;
      let e = null;
      if (!isP(';')) e = expr();
      eatP(';');
      return {kind:'return', e, line: t.line};
    }
    if (isKw('break')){ pos++; eatP(';'); return {kind:'break', line: t.line}; }
    if (isKw('continue')){ pos++; eatP(';'); return {kind:'continue', line: t.line}; }
    if (isP(';')){ pos++; return {kind:'block', body: [], line: t.line}; }
    if (isTypeStart()) return declStmt();
    const e = expr(); eatP(';');
    return {kind:'exprstmt', e, line: t.line};
  }

  // ---- top level ----
  function constExpr(){
    let sign = 1;
    if (isP('-')){ pos++; sign = -1; }
    const t = next();
    if (t.type !== 'num') throw CErr('global initialisers must be constant', t.line);
    return (sign * t.val) | 0;
  }

  while (tok().type !== 'eof'){
    const line = tok().line;
    const base = parseBaseType();
    let ty = parseStars(base);
    const nameTok = next();
    if (nameTok.type !== 'ident') throw CErr('expected a name', nameTok.line);

    if (isP('(')){
      // function definition or prototype
      pos++;
      const params = [];
      if (!isP(')')){
        if (isKw('void') && peek(1).type === 'punct' && peek(1).val === ')'){ pos++; }
        else for (;;){
          const pb = parseBaseType();
          let pt = parseStars(pb);
          const pn = next();
          if (pn.type !== 'ident') throw CErr('expected a parameter name', pn.line);
          if (isP('[')){ pos++; eatP(']'); pt = ptrTo(pt); } // array param decays
          if (pt.kind === 'void') throw CErr('parameters cannot have type void', pn.line);
          params.push({name: pn.val, type: pt});
          if (isP(',')){ pos++; continue; }
          break;
        }
      }
      eatP(')');
      if (params.length > 8) throw CErr('at most 8 parameters are supported', line);
      const fn = funcMap.get(nameTok.val) || {name: nameTok.val, retType: ty, params, locals: [], body: null};
      funcMap.set(nameTok.val, fn);
      if (isP(';')){ pos++; continue; } // prototype
      if (fn.body) throw CErr(`redefinition of '${nameTok.val}'`, line);
      curFn = fn;
      fn.locals = [];
      scopes = [new Map()];
      fn.paramVars = params.map(p => newLocal(p.name, p.type, line));
      if (!isP('{')) throw CErr('expected a function body', tok().line);
      fn.body = stmt();
      scopes = [];
      curFn = null;
      prog.funcs.push(fn);
      continue;
    }

    // global variable(s)
    for (;;){
      let gty = ty;
      if (isP('[')){
        pos++;
        const lenTok = next();
        if (lenTok.type !== 'num' || lenTok.val <= 0) throw CErr('array length must be a positive constant', lenTok.line);
        eatP(']');
        gty = arrOf(gty, lenTok.val);
      }
      if (gty.kind === 'void') throw CErr('variables cannot have type void', nameTok.line);
      if (globalMap.has(nameTok.val)) throw CErr(`redeclaration of '${nameTok.val}'`, nameTok.line);
      const g = {name: nameTok.val, type: gty, isLocal: false, init: null};
      if (isP('=')){
        pos++;
        if (gty.kind === 'array'){
          eatP('{');
          const vals = [];
          if (!isP('}')){
            vals.push(constExpr());
            while (isP(',')){ pos++; if (isP('}')) break; vals.push(constExpr()); }
          }
          eatP('}');
          if (vals.length > gty.len) throw CErr('too many initialisers', nameTok.line);
          g.init = vals;
        } else {
          g.init = constExpr();
        }
      }
      globalMap.set(g.name, g);
      prog.globals.push(g);
      if (isP(',')){
        pos++;
        ty = parseStars(base);
        const nt = next();
        if (nt.type !== 'ident') throw CErr('expected a name', nt.line);
        nameTok.val = nt.val; nameTok.line = nt.line;
        continue;
      }
      eatP(';');
      break;
    }
  }

  if (!funcMap.has('main') || !funcMap.get('main').body) throw CErr('no main() function is defined', 1);
  return prog;
}

// ---------------- Code generation ----------------
function codegen(prog, cSrc){
  const out = [];
  const cLines = cSrc.split('\n');
  let labelN = 0;
  let curFn = null;
  const brk = [], cont = [];
  function L(){ return `.L${labelN++}`; }
  function emit(s){ out.push('  ' + s); }
  function emitLabel(s){ out.push(s + ':'); }
  function emitSrc(line){
    if (line >= 1 && line <= cLines.length){
      const txt = cLines[line - 1].trim();
      if (txt) out.push(`                                # C:${line}  ${txt}`.replace(/^ +#/, '  #'));
    }
  }
  const push = () => { emit('addi sp, sp, -4'); emit('sw a0, 0(sp)'); };
  const pop = (r) => { emit(`lw ${r}, 0(sp)`); emit('addi sp, sp, 4'); };

  function load(type){
    if (type.kind === 'array') return;            // address *is* the value
    emit(type.kind === 'char' ? 'lb a0, 0(a0)' : 'lw a0, 0(a0)');
  }
  function store(type){                            // addr in a1, value in a0
    emit(type.kind === 'char' ? 'sb a0, 0(a1)' : 'sw a0, 0(a1)');
  }
  function scaleLog2(t){ return sizeOf(baseOf(t)) === 4 ? 2 : 0; }

  function genAddr(node){
    if (node.kind === 'var'){
      const v = node.v;
      if (v.isLocal){
        if (v.offset >= -2048) emit(`addi a0, s0, ${v.offset}`);
        else { emit(`li a0, ${v.offset}`); emit('add a0, s0, a0'); }
      } else {
        emit(`la a0, ${v.name}`);
      }
      return;
    }
    if (node.kind === 'deref'){ genExpr(node.e); return; }
    if (node.kind === 'str'){ emit(`la a0, .str${node.idx}`); return; }
    throw CErr('expression is not addressable', node.line);
  }

  function emitBin(op, ltype, rtype){              // a0 = a0 OP a1
    switch (op){
      case '+':
        if (isPtrLike(ltype)){ const s = scaleLog2(ltype); if (s) emit(`slli a1, a1, ${s}`); }
        emit('add a0, a0, a1'); break;
      case '-':
        if (isPtrLike(ltype) && isPtrLike(rtype)){
          emit('sub a0, a0, a1');
          const s = scaleLog2(ltype); if (s) emit(`srai a0, a0, ${s}`);
        } else if (isPtrLike(ltype)){
          const s = scaleLog2(ltype); if (s) emit(`slli a1, a1, ${s}`);
          emit('sub a0, a0, a1');
        } else emit('sub a0, a0, a1');
        break;
      case '*': emit('mul a0, a0, a1'); break;
      case '/': emit('div a0, a0, a1'); break;
      case '%': emit('rem a0, a0, a1'); break;
      case '&': emit('and a0, a0, a1'); break;
      case '|': emit('or a0, a0, a1'); break;
      case '^': emit('xor a0, a0, a1'); break;
      case '<<': emit('sll a0, a0, a1'); break;
      case '>>': emit('sra a0, a0, a1'); break;
      case '==': emit('sub a0, a0, a1'); emit('seqz a0, a0'); break;
      case '!=': emit('sub a0, a0, a1'); emit('snez a0, a0'); break;
      case '<':  emit('slt a0, a0, a1'); break;
      case '>':  emit('slt a0, a1, a0'); break;
      case '<=': emit('slt a0, a1, a0'); emit('xori a0, a0, 1'); break;
      case '>=': emit('slt a0, a0, a1'); emit('xori a0, a0, 1'); break;
      default: throw CErr(`operator '${op}' is not supported`, 0);
    }
  }

  function genExpr(node){
    switch (node.kind){
      case 'num': emit(`li a0, ${node.val}`); return;
      case 'str': emit(`la a0, .str${node.idx}`); return;
      case 'var': genAddr(node); load(node.type); return;
      case 'deref': genExpr(node.e); load(node.type); return;
      case 'addr': genAddr(node.e); return;
      case 'neg': genExpr(node.e); emit('neg a0, a0'); return;
      case 'bitnot': genExpr(node.e); emit('not a0, a0'); return;
      case 'lognot': genExpr(node.e); emit('seqz a0, a0'); return;
      case 'assign':
        genAddr(node.l); push();
        genExpr(node.r); pop('a1');
        store(node.l.type);
        return;
      case 'opassign': {
        genAddr(node.l); push();                   // stack: [addr]
        load(node.l.type); push();                 // stack: [addr, lhsval]
        genExpr(node.r);                            // a0 = rhs
        emit('mv a1, a0');
        pop('a0');                                  // a0 = lhsval
        emitBin(node.op, node.l.type, node.r.type);
        pop('a1');                                  // a1 = addr
        store(node.l.type);
        return;
      }
      case 'preincdec': case 'postincdec': {
        const step = isPtrLike(node.e.type) ? sizeOf(baseOf(node.e.type)) : 1;
        const d = node.op === '++' ? step : -step;
        genAddr(node.e);
        emit(node.e.type.kind === 'char' ? 'lb a1, 0(a0)' : 'lw a1, 0(a0)');
        emit(`addi a2, a1, ${d}`);
        emit(node.e.type.kind === 'char' ? 'sb a2, 0(a0)' : 'sw a2, 0(a0)');
        emit(node.kind === 'preincdec' ? 'mv a0, a2' : 'mv a0, a1');
        return;
      }
      case 'bin':
        genExpr(node.r); push();
        genExpr(node.l); pop('a1');
        emitBin(node.op, node.l.type, node.r.type);
        return;
      case 'logand': {
        const lf = L(), le = L();
        genExpr(node.l); emit(`beqz a0, ${lf}`);
        genExpr(node.r); emit(`beqz a0, ${lf}`);
        emit('li a0, 1'); emit(`j ${le}`);
        emitLabel(lf); emit('li a0, 0');
        emitLabel(le); return;
      }
      case 'logor': {
        const lt = L(), le = L();
        genExpr(node.l); emit(`bnez a0, ${lt}`);
        genExpr(node.r); emit(`bnez a0, ${lt}`);
        emit('li a0, 0'); emit(`j ${le}`);
        emitLabel(lt); emit('li a0, 1');
        emitLabel(le); return;
      }
      case 'cond': {
        const lb = L(), le = L();
        genExpr(node.c); emit(`beqz a0, ${lb}`);
        genExpr(node.a); emit(`j ${le}`);
        emitLabel(lb); genExpr(node.b);
        emitLabel(le); return;
      }
      case 'builtin': {
        if (node.args.length === 1) genExpr(node.args[0]);   // result already lands in a0
        emit(`li a7, ${node.svc}`);
        emit('ecall');
        return;
      }
      case 'call': {
        for (const a of node.args){ genExpr(a); push(); }
        for (let i = node.args.length - 1; i >= 0; i--) pop(`a${i}`);
        emit(`call ${node.name}`);
        return;
      }
      default: throw CErr(`cannot generate code for '${node.kind}'`, node.line);
    }
  }

  function genStmt(node){
    switch (node.kind){
      case 'block': for (const s of node.body) genStmt(s); return;
      case 'exprstmt': emitSrc(node.line); genExpr(node.e); return;
      case 'decl':
        for (const it of node.items){
          if (it.init){
            emitSrc(it.line);
            genAddr({kind:'var', v: it.v, type: it.v.type, line: it.line}); push();
            genExpr(it.init); pop('a1');
            store(it.v.type);
          }
        }
        return;
      case 'if': {
        emitSrc(node.line);
        const le = L(), lend = L();
        genExpr(node.c); emit(`beqz a0, ${le}`);
        genStmt(node.then);
        if (node.els){ emit(`j ${lend}`); emitLabel(le); genStmt(node.els); emitLabel(lend); }
        else emitLabel(le);
        return;
      }
      case 'while': {
        emitSrc(node.line);
        const lb = L(), lend = L();
        cont.push(lb); brk.push(lend);
        emitLabel(lb);
        genExpr(node.c); emit(`beqz a0, ${lend}`);
        genStmt(node.body);
        emit(`j ${lb}`);
        emitLabel(lend);
        cont.pop(); brk.pop();
        return;
      }
      case 'for': {
        emitSrc(node.line);
        const lb = L(), lc = L(), lend = L();
        if (node.init) genStmt(node.init.kind ? node.init : {kind:'exprstmt', e: node.init, line: node.line});
        cont.push(lc); brk.push(lend);
        emitLabel(lb);
        if (node.c){ genExpr(node.c); emit(`beqz a0, ${lend}`); }
        genStmt(node.body);
        emitLabel(lc);
        if (node.inc) genExpr(node.inc);
        emit(`j ${lb}`);
        emitLabel(lend);
        cont.pop(); brk.pop();
        return;
      }
      case 'return':
        emitSrc(node.line);
        if (node.e) genExpr(node.e);
        emit(`j .Lret_${curFn.name}`);
        return;
      case 'break':
        if (!brk.length) throw CErr("'break' outside a loop", node.line);
        emit(`j ${brk[brk.length - 1]}`); return;
      case 'continue':
        if (!cont.length) throw CErr("'continue' outside a loop", node.line);
        emit(`j ${cont[cont.length - 1]}`); return;
      default: throw CErr(`cannot generate code for statement '${node.kind}'`, node.line);
    }
  }

  // ---- startup ----
  out.push('# Generated by the RV32 Workbench C compiler');
  out.push('.text');
  emitLabel('_start');
  emit('li sp, 0x10000                 # stack top');
  emit('call main');
  emit('li a7, 93                      # exit(main return value)');
  emit('ecall');

  for (const fn of prog.funcs){
    curFn = fn;
    // assign local offsets: ra at -4(s0), saved s0 at -8(s0), locals below
    let off = -8;
    for (const v of fn.locals){
      const sz = Math.max(4, Math.ceil(sizeOf(v.type) / 4) * 4);
      off -= sz;
      v.offset = off;
    }
    const frame = Math.ceil((-off + 8) / 16) * 16;
    out.push('');
    out.push(`# ---- ${fn.retType.kind} ${fn.name}(${fn.params.map(p=>p.name).join(', ')}) ----`);
    emitLabel(fn.name);
    if (frame <= 2032){
      emit(`addi sp, sp, -${frame}`);
      emit(`sw ra, ${frame - 4}(sp)`);
      emit(`sw s0, ${frame - 8}(sp)`);
      emit(`addi s0, sp, ${frame}`);
    } else {
      emit(`li t0, ${frame}`);
      emit('sub sp, sp, t0');
      emit('add t1, sp, t0');
      emit('sw ra, -4(t1)');
      emit('sw s0, -8(t1)');
      emit('mv s0, t1');
    }
    fn.paramVars.forEach((v, i) => {
      if (v.offset >= -2048) emit(`sw a${i}, ${v.offset}(s0)`);
      else { emit(`li t0, ${v.offset}`); emit('add t0, s0, t0'); emit(`sw a${i}, 0(t0)`); }
    });
    genStmt(fn.body);
    emit('li a0, 0');
    emitLabel(`.Lret_${fn.name}`);
    emit('lw ra, -4(s0)');
    emit('mv t0, s0');
    emit('lw s0, -8(s0)');
    emit('mv sp, t0');
    emit('ret');
  }

  // ---- data ----
  if (prog.globals.length || prog.strings.length){
    out.push('');
    out.push('.data');
    for (const g of prog.globals){
      if (g.type.kind === 'array'){
        const elems = g.type.len;
        const init = g.init || [];
        if (g.type.base.kind === 'char'){
          out.push(`${g.name}: .zero ${elems}`);
        } else if (init.length){
          const vals = init.concat(new Array(elems - init.length).fill(0));
          out.push(`${g.name}: .word ${vals.join(', ')}`);
        } else {
          out.push(`${g.name}: .zero ${elems * 4}`);
        }
      } else if (g.type.kind === 'char'){
        out.push(`${g.name}: .byte ${g.init === null ? 0 : g.init & 0xff}`);
      } else {
        out.push(`${g.name}: .word ${g.init === null ? 0 : g.init}`);
      }
    }
    prog.strings.forEach((s, i) => {
      out.push(`.str${i}: .asciiz "${s.replace(/\\/g,'\\\\').replace(/"/g,'\\"').replace(/\n/g,'\\n').replace(/\t/g,'\\t').replace(/\r/g,'\\r').replace(/\0/g,'\\0')}"`);
    });
  }

  return out.join('\n');
}

function compileC(src){
  return codegen(parse(tokenize(src)), src);
}

// ---------------- Assembler (RV32IM + pseudo-instructions) ----------------
const TEXT_BASE = 0x0000;
const DATA_BASE = 0x4000;
const MEM_SIZE  = 0x10000;   // 64 KiB; stack grows down from the top

// Memory-mapped virtual display (MMIO window sitting just above RAM)
const DISP_W = 64, DISP_H = 64;
const DISP_FB = MEM_SIZE;                    // 0x10000  framebuffer base
const DISP_FB_SIZE = DISP_W * DISP_H;        // 4096 bytes, one per pixel (RGB332)
const DISP_CTL = DISP_FB + DISP_FB_SIZE;     // 0x11000  write a byte -> flood-fill / clear
const DISP_TOP = DISP_CTL + 4;               // 0x11004  end of MMIO window (exclusive)

const REG_NAMES = {};
(function(){
  const abi = ['zero','ra','sp','gp','tp','t0','t1','t2','s0','s1',
               'a0','a1','a2','a3','a4','a5','a6','a7',
               's2','s3','s4','s5','s6','s7','s8','s9','s10','s11',
               't3','t4','t5','t6'];
  abi.forEach((n, i) => REG_NAMES[n] = i);
  for (let i = 0; i < 32; i++) REG_NAMES['x' + i] = i;
  REG_NAMES['fp'] = 8;
})();
const ABI = ['zero','ra','sp','gp','tp','t0','t1','t2','s0','s1','a0','a1','a2','a3','a4','a5','a6','a7','s2','s3','s4','s5','s6','s7','s8','s9','s10','s11','t3','t4','t5','t6'];

function AErr(msg, line){ const e = new Error(msg); e.aline = line; e.isAsm = true; return e; }

function parseReg(s, line){
  const r = REG_NAMES[s];
  if (r === undefined) throw AErr(`'${s}' is not a register`, line);
  return r;
}
function parseImm(s, line, syms){
  s = s.trim();
  if (/^-?0x[0-9a-fA-F]+$/.test(s)) return parseInt(s, 16) | 0;
  if (/^-?\d+$/.test(s)) return parseInt(s, 10) | 0;
  if (syms && syms.has(s)) return syms.get(s);
  throw AErr(syms ? `'${s}' is not a number or a known label` : `'${s}' is not a number`, line);
}
const sx12 = v => (v << 20) >> 20;
function hi20(v){ return ((v + 0x800) >>> 12) & 0xFFFFF; }
function lo12(v){ return sx12(v & 0xFFF); }

// instruction encoders
const encR = (f7,rs2,rs1,f3,rd,op) => ((f7<<25)|(rs2<<20)|(rs1<<15)|(f3<<12)|(rd<<7)|op)>>>0;
const encI = (imm,rs1,f3,rd,op) => (((imm&0xFFF)<<20)|(rs1<<15)|(f3<<12)|(rd<<7)|op)>>>0;
const encS = (imm,rs2,rs1,f3,op) => ((((imm>>5)&0x7F)<<25)|(rs2<<20)|(rs1<<15)|(f3<<12)|((imm&0x1F)<<7)|op)>>>0;
const encB = (imm,rs2,rs1,f3,op) => ((((imm>>12)&1)<<31)|(((imm>>5)&0x3F)<<25)|(rs2<<20)|(rs1<<15)|(f3<<12)|(((imm>>1)&0xF)<<8)|(((imm>>11)&1)<<7)|op)>>>0;
const encU = (imm,rd,op) => (((imm&0xFFFFF)<<12)|(rd<<7)|op)>>>0;
const encJ = (imm,rd,op) => ((((imm>>20)&1)<<31)|(((imm>>1)&0x3FF)<<21)|(((imm>>11)&1)<<20)|(((imm>>12)&0xFF)<<12)|(rd<<7)|op)>>>0;

const RTYPE = { add:[0,0], sub:[0x20,0], sll:[0,1], slt:[0,2], sltu:[0,3], xor:[0,4], srl:[0,5], sra:[0x20,5], or:[0,6], and:[0,7],
  mul:[1,0], mulh:[1,1], mulhsu:[1,2], mulhu:[1,3], div:[1,4], divu:[1,5], rem:[1,6], remu:[1,7] };
const ITYPE = { addi:0, slti:2, sltiu:3, xori:4, ori:6, andi:7 };
const SHIFTI = { slli:[0,1], srli:[0,5], srai:[0x20,5] };
const LOADS = { lb:0, lh:1, lw:2, lbu:4, lhu:5 };
const STORES = { sb:0, sh:1, sw:2 };
const BRANCH = { beq:0, bne:1, blt:4, bge:5, bltu:6, bgeu:7 };
// A extension: funct5 values (opcode 0x2F, funct3=2, aq/rl bits left clear)
const AMO = { 'sc.w':0x03, 'amoadd.w':0x00, 'amoswap.w':0x01, 'amoxor.w':0x04, 'amoor.w':0x08,
  'amoand.w':0x0C, 'amomin.w':0x10, 'amomax.w':0x14, 'amominu.w':0x18, 'amomaxu.w':0x1C };
const M_OPS = new Set(['mul','mulh','mulhsu','mulhu','div','divu','rem','remu']);

function splitOperands(rest){
  return rest.length ? rest.split(',').map(s => s.trim()).filter(s => s.length) : [];
}
function parseMemOp(s, line){    // "imm(reg)" or "(reg)"
  const m = s.match(/^(-?\w*)\s*\(\s*(\w+)\s*\)$/);
  if (!m) throw AErr(`'${s}' is not a valid memory operand (expected offset(register))`, line);
  const off = m[1] === '' ? 0 : parseImm(m[1], line);
  return {off, reg: parseReg(m[2], line)};
}

function unescapeAsm(s){
  return s.replace(/\\(.)/g, (_, c) => ({n:'\n',t:'\t',r:'\r','0':'\0','\\':'\\','"':'"'}[c] ?? c));
}

// expand one mnemonic into 1..2 concrete records {op, args..., needsSym?}
function assemble(src, isa = 'IMA'){
  const lines = src.split('\n');
  const items = [];          // {kind:'instr'|'data', ...}
  const syms = new Map();
  let section = 'text';
  let textPC = TEXT_BASE;
  const dataBytes = [];
  let dataPC = DATA_BASE;
  const wordFixups = [];     // {at, sym, line}: .word operands naming labels, patched after pass 1

  // ---------- pass 1: layout ----------
  for (let ln = 0; ln < lines.length; ln++){
    let s = lines[ln];
    const hash = s.indexOf('#');
    if (hash >= 0) s = s.slice(0, hash);
    s = s.trim();
    if (!s) continue;

    // labels (possibly several) at line start
    let m;
    while ((m = s.match(/^([A-Za-z_.][\w.]*)\s*:\s*/))){
      const name = m[1];
      if (syms.has(name)) throw AErr(`label '${name}' is defined twice`, ln + 1);
      syms.set(name, section === 'text' ? textPC : dataPC);
      s = s.slice(m[0].length);
    }
    if (!s) continue;

    if (s[0] === '.'){
      const dm = s.match(/^(\.\w+)\s*(.*)$/);
      const dir = dm[1], rest = dm[2];
      if (dir === '.text'){ section = 'text'; continue; }
      if (dir === '.data'){ section = 'data'; continue; }
      if (dir === '.word'){
        if (section !== 'data') throw AErr('.word is only allowed in the .data section', ln + 1);
        for (const v of splitOperands(rest)){
          let x = 0;
          if (/^-?(0x[0-9a-fA-F]+|\d+)$/i.test(v)) x = parseImm(v, ln + 1);
          else wordFixups.push({at: dataBytes.length, sym: v, line: ln + 1});
          dataBytes.push(x & 0xFF, (x >> 8) & 0xFF, (x >> 16) & 0xFF, (x >> 24) & 0xFF);
          dataPC += 4;
        }
        continue;
      }
      if (dir === '.half'){
        if (section !== 'data') throw AErr('.half is only allowed in the .data section', ln + 1);
        for (const v of splitOperands(rest)){
          const x = parseImm(v, ln + 1);
          dataBytes.push(x & 0xFF, (x >> 8) & 0xFF);
          dataPC += 2;
        }
        continue;
      }
      if (dir === '.byte'){
        if (section !== 'data') throw AErr('.byte is only allowed in the .data section', ln + 1);
        for (const v of splitOperands(rest)){ dataBytes.push(parseImm(v, ln + 1) & 0xFF); dataPC++; }
        continue;
      }
      if (dir === '.zero' || dir === '.space'){
        if (section !== 'data') throw AErr(`${dir} is only allowed in the .data section`, ln + 1);
        const cnt = parseImm(rest, ln + 1);
        for (let i = 0; i < cnt; i++) dataBytes.push(0);
        dataPC += cnt;
        continue;
      }
      if (dir === '.align'){
        const n = parseImm(rest, ln + 1);
        if (n < 0 || n > 12) throw AErr('.align expects an exponent 0..12 (aligns to 2^n bytes)', ln + 1);
        const a = 1 << n;
        if (section === 'data'){ while (dataPC % a){ dataBytes.push(0); dataPC++; } }
        else if (a > 4) throw AErr('.align beyond 4-byte units is not supported in .text', ln + 1);
        continue;
      }
      if (dir === '.asciiz' || dir === '.string'){
        if (section !== 'data') throw AErr(`${dir} is only allowed in the .data section`, ln + 1);
        const sm = rest.match(/^"((?:[^"\\]|\\.)*)"$/);
        if (!sm) throw AErr('expected a quoted string', ln + 1);
        const bytes = unescapeAsm(sm[1]);
        for (const ch of bytes){ dataBytes.push(ch.charCodeAt(0) & 0xFF); dataPC++; }
        dataBytes.push(0); dataPC++;
        continue;
      }
      if (dir === '.globl' || dir === '.global') continue;  // tolerated
      throw AErr(`unknown directive '${dir}'`, ln + 1);
    }

    if (section !== 'text') throw AErr('instructions are only allowed in the .text section', ln + 1);
    const im = s.match(/^([A-Za-z.]+)\s*(.*)$/);
    if (!im) throw AErr(`cannot parse '${s}'`, ln + 1);
    const op = im[1].toLowerCase();
    const ops = splitOperands(im[2]);
    // size in instructions (li can be 1 or 2; la/call sized here)
    let size = 1;
    if (op === 'li'){
      if (ops.length !== 2) throw AErr('li needs 2 operands', ln + 1);
      const v = parseImm(ops[1], ln + 1);
      size = (v >= -2048 && v <= 2047) ? 1 : 2;
    } else if (op === 'la'){
      size = 2;
    }
    items.push({kind:'instr', op, ops, line: ln + 1, pc: textPC, size});
    textPC += size * 4;
  }

  if (textPC > DATA_BASE) throw AErr(`program text is too large (${textPC} bytes; limit ${DATA_BASE})`, 1);
  if (dataPC > MEM_SIZE - 1024) throw AErr('data section is too large', 1);

  for (const f of wordFixups){
    if (!syms.has(f.sym)) throw AErr(`'${f.sym}' is not a number or a known label`, f.line);
    const x = syms.get(f.sym);
    dataBytes[f.at] = x & 0xFF; dataBytes[f.at + 1] = (x >> 8) & 0xFF;
    dataBytes[f.at + 2] = (x >> 16) & 0xFF; dataBytes[f.at + 3] = (x >> 24) & 0xFF;
  }

  // ---------- pass 2: encode ----------
  const words = [];      // {word, pc, line}

  for (const it of items){
    const {op, ops, line, pc} = it;
    const ext = M_OPS.has(op) ? 'M' : (op === 'lr.w' || op in AMO) ? 'A' : null;
    if (ext && !isa.includes(ext)) throw AErr(`'${op}' requires the ${ext} extension (current ISA is RV32${isa})`, line);
    const W = [];
    const reg = i => parseReg(ops[i], line);
    const imm = i => parseImm(ops[i], line, syms);
    const need = (n) => { if (ops.length !== n) throw AErr(`${op} needs ${n} operand(s), got ${ops.length}`, line); };
    const branchTo = (target, atPC) => {
      const off = target - atPC;
      if (off < -4096 || off > 4094 || (off & 1)) throw AErr('branch target is out of range', line);
      return off;
    };

    if (op in RTYPE){ need(3); const [f7, f3] = RTYPE[op]; W.push(encR(f7, reg(2), reg(1), f3, reg(0), 0x33)); }
    else if (op in ITYPE){ need(3); const v = imm(2); if (v < -2048 || v > 2047) throw AErr(`immediate ${v} does not fit in 12 bits`, line); W.push(encI(v, reg(1), ITYPE[op], reg(0), 0x13)); }
    else if (op in SHIFTI){ need(3); const [f7, f3] = SHIFTI[op]; const sh = imm(2); if (sh < 0 || sh > 31) throw AErr('shift amount must be 0..31', line); W.push(encI((f7 << 5) | sh, reg(1), f3, reg(0), 0x13)); }
    else if (op in LOADS){ need(2); const mo = parseMemOp(ops[1], line); if (mo.off < -2048 || mo.off > 2047) throw AErr('load offset out of range', line); W.push(encI(mo.off, mo.reg, LOADS[op], reg(0), 0x03)); }
    else if (op in STORES){ need(2); const mo = parseMemOp(ops[1], line); if (mo.off < -2048 || mo.off > 2047) throw AErr('store offset out of range', line); W.push(encS(mo.off, reg(0), mo.reg, STORES[op], 0x23)); }
    else if (op in BRANCH){ need(3); W.push(encB(branchTo(imm(2), pc), reg(1), reg(0), BRANCH[op], 0x63)); }
    else if (op === 'lui'){ need(2); W.push(encU(imm(1), reg(0), 0x37)); }
    else if (op === 'auipc'){ need(2); W.push(encU(imm(1), reg(0), 0x17)); }
    else if (op === 'jal'){
      let rd = 1, target;
      if (ops.length === 1) target = imm(0);
      else { need(2); rd = reg(0); target = imm(1); }
      const off = target - pc;
      if (off < -(1 << 20) || off >= (1 << 20)) throw AErr('jal target is out of range', line);
      W.push(encJ(off, rd, 0x6F));
    }
    else if (op === 'jalr'){
      if (ops.length === 1) W.push(encI(0, reg(0), 0, 1, 0x67));
      else if (ops.length === 2 && ops[1].includes('(')){ const mo = parseMemOp(ops[1], line); W.push(encI(mo.off, mo.reg, 0, reg(0), 0x67)); }
      else { need(3); W.push(encI(imm(2), reg(1), 0, reg(0), 0x67)); }
    }
    else if (op === 'ecall'){ W.push(encI(0, 0, 0, 0, 0x73)); }
    else if (op === 'ebreak'){ W.push(encI(1, 0, 0, 0, 0x73)); }
    // ---- A extension ----
    else if (op === 'lr.w'){
      need(2);
      const mo = parseMemOp(ops[1], line);
      if (mo.off) throw AErr('lr.w takes no offset: lr.w rd, (rs1)', line);
      W.push(encR(0x02 << 2, 0, mo.reg, 2, reg(0), 0x2F));
    }
    else if (op in AMO){
      need(3);
      const mo = parseMemOp(ops[2], line);
      if (mo.off) throw AErr(`${op} takes no offset: ${op} rd, rs2, (rs1)`, line);
      W.push(encR(AMO[op] << 2, reg(1), mo.reg, 2, reg(0), 0x2F));
    }
    // ---- pseudo-instructions ----
    else if (op === 'nop'){ W.push(encI(0, 0, 0, 0, 0x13)); }
    else if (op === 'li'){
      const rd = reg(0), v = imm(1);
      if (it.size === 1) W.push(encI(v, 0, 0, rd, 0x13));
      else { W.push(encU(hi20(v), rd, 0x37)); W.push(encI(lo12(v), rd, 0, rd, 0x13)); }
    }
    else if (op === 'la'){
      need(2);
      const rd = reg(0), v = imm(1);
      W.push(encU(hi20(v), rd, 0x37));
      W.push(encI(lo12(v), rd, 0, rd, 0x13));
    }
    else if (op === 'mv'){ need(2); W.push(encI(0, reg(1), 0, reg(0), 0x13)); }
    else if (op === 'not'){ need(2); W.push(encI(-1, reg(1), 4, reg(0), 0x13)); }
    else if (op === 'neg'){ need(2); W.push(encR(0x20, reg(1), 0, 0, reg(0), 0x33)); }
    else if (op === 'seqz'){ need(2); W.push(encI(1, reg(1), 3, reg(0), 0x13)); }
    else if (op === 'snez'){ need(2); W.push(encR(0, reg(1), 0, 3, reg(0), 0x33)); }
    else if (op === 'sltz'){ need(2); W.push(encR(0, 0, reg(1), 2, reg(0), 0x33)); }
    else if (op === 'sgtz'){ need(2); W.push(encR(0, reg(1), 0, 2, reg(0), 0x33)); }
    else if (op === 'j'){ need(1); const off = imm(0) - pc; if (off < -(1<<20) || off >= (1<<20)) throw AErr('jump target out of range', line); W.push(encJ(off, 0, 0x6F)); }
    else if (op === 'jr'){ need(1); W.push(encI(0, reg(0), 0, 0, 0x67)); }
    else if (op === 'ret'){ W.push(encI(0, 1, 0, 0, 0x67)); }
    else if (op === 'call'){ need(1); const off = imm(0) - pc; if (off < -(1<<20) || off >= (1<<20)) throw AErr('call target out of range', line); W.push(encJ(off, 1, 0x6F)); }
    else if (op === 'beqz'){ need(2); W.push(encB(branchTo(imm(1), pc), 0, reg(0), 0, 0x63)); }
    else if (op === 'bnez'){ need(2); W.push(encB(branchTo(imm(1), pc), 0, reg(0), 1, 0x63)); }
    else if (op === 'blez'){ need(2); W.push(encB(branchTo(imm(1), pc), reg(0), 0, 5, 0x63)); }
    else if (op === 'bgez'){ need(2); W.push(encB(branchTo(imm(1), pc), 0, reg(0), 5, 0x63)); }
    else if (op === 'bltz'){ need(2); W.push(encB(branchTo(imm(1), pc), 0, reg(0), 4, 0x63)); }
    else if (op === 'bgtz'){ need(2); W.push(encB(branchTo(imm(1), pc), reg(0), 0, 4, 0x63)); }
    else if (op === 'ble'){ need(3); W.push(encB(branchTo(imm(2), pc), reg(0), reg(1), 5, 0x63)); }
    else if (op === 'bgt'){ need(3); W.push(encB(branchTo(imm(2), pc), reg(0), reg(1), 4, 0x63)); }
    else if (op === 'bleu'){ need(3); W.push(encB(branchTo(imm(2), pc), reg(0), reg(1), 7, 0x63)); }
    else if (op === 'bgtu'){ need(3); W.push(encB(branchTo(imm(2), pc), reg(0), reg(1), 6, 0x63)); }
    else throw AErr(`unknown instruction '${op}'`, line);

    if (W.length !== it.size) throw AErr(`internal sizing error for '${op}'`, line);
    W.forEach((w, k) => words.push({word: w >>> 0, pc: pc + k * 4, line}));
  }

  return {words, dataBytes, symbols: syms, textSize: textPC - TEXT_BASE, dataSize: dataBytes.length};
}

// ---------------- Disassembler (for the listing pane) ----------------
function disasm(w, pc){
  const op = w & 0x7F, rd = (w >> 7) & 0x1F, f3 = (w >> 12) & 7, rs1 = (w >> 15) & 0x1F, rs2 = (w >> 20) & 0x1F, f7 = (w >> 25) & 0x7F;
  const iImm = (w | 0) >> 20;
  const r = i => ABI[i];
  switch (op){
    case 0x33: {
      const names = f7 === 1 ? ['mul','mulh','mulhsu','mulhu','div','divu','rem','remu']
        : {0:['add','sll','slt','sltu','xor','srl','or','and'], 0x20:{0:'sub',5:'sra'}}[f7];
      let n;
      if (f7 === 1) n = names[f3];
      else if (f7 === 0) n = names[f3];
      else if (f7 === 0x20) n = f3 === 0 ? 'sub' : 'sra';
      return `${n} ${r(rd)}, ${r(rs1)}, ${r(rs2)}`;
    }
    case 0x13: {
      if (f3 === 1) return `slli ${r(rd)}, ${r(rs1)}, ${rs2}`;
      if (f3 === 5) return `${f7 === 0x20 ? 'srai' : 'srli'} ${r(rd)}, ${r(rs1)}, ${rs2}`;
      const n = ['addi','?','slti','sltiu','xori','?','ori','andi'][f3];
      return `${n} ${r(rd)}, ${r(rs1)}, ${iImm}`;
    }
    case 0x03: return `${['lb','lh','lw','?','lbu','lhu'][f3]} ${r(rd)}, ${iImm}(${r(rs1)})`;
    case 0x23: {
      const sImm = ((w >> 7) & 0x1F) | (((w | 0) >> 25) << 5);
      return `${['sb','sh','sw'][f3]} ${r(rs2)}, ${sImm}(${r(rs1)})`;
    }
    case 0x63: {
      const bImm = (((w >> 8) & 0xF) << 1) | (((w >> 25) & 0x3F) << 5) | (((w >> 7) & 1) << 11) | ((((w | 0) >> 31)) << 12);
      return `${['beq','bne','?','?','blt','bge','bltu','bgeu'][f3]} ${r(rs1)}, ${r(rs2)}, 0x${((pc + bImm) >>> 0).toString(16)}`;
    }
    case 0x37: return `lui ${r(rd)}, 0x${((w >>> 12)).toString(16)}`;
    case 0x17: return `auipc ${r(rd)}, 0x${((w >>> 12)).toString(16)}`;
    case 0x6F: {
      let j = (((w >> 21) & 0x3FF) << 1) | (((w >> 20) & 1) << 11) | (((w >> 12) & 0xFF) << 12) | ((((w | 0) >> 31)) << 20);
      return `jal ${r(rd)}, 0x${((pc + j) >>> 0).toString(16)}`;
    }
    case 0x67: return `jalr ${r(rd)}, ${iImm}(${r(rs1)})`;
    case 0x73: return iImm === 1 ? 'ebreak' : 'ecall';
    case 0x2F: {
      const f5 = (w >>> 27) & 0x1F;
      const names = {0:'amoadd.w',1:'amoswap.w',2:'lr.w',3:'sc.w',4:'amoxor.w',8:'amoor.w',12:'amoand.w',16:'amomin.w',20:'amomax.w',24:'amominu.w',28:'amomaxu.w'};
      const n = names[f5];
      if (!n || f3 !== 2) return `.word 0x${w.toString(16).padStart(8,'0')}`;
      return f5 === 2 ? `lr.w ${r(rd)}, (${r(rs1)})` : `${n} ${r(rd)}, ${r(rs2)}, (${r(rs1)})`;
    }
    default: return `.word 0x${w.toString(16).padStart(8,'0')}`;
  }
}

// ---------------- CPU ----------------
class CPU {
  constructor(){
    this.mem = new Uint8Array(MEM_SIZE);
    this.view = new DataView(this.mem.buffer);
    this.regs = new Int32Array(32);
    this.pc = TEXT_BASE;
    this.halted = false;
    this.haltReason = '';
    this.exitCode = null;
    this.instret = 0;
    this.onPrint = () => {};
    this.waitingInput = false;   // stalled on read_int; resume with provideInput()
    this.lastWrites = [];     // [addr, len] of memory writes in the most recent step
    this.lastRegWrite = -1;
    this.isaM = true; this.isaA = true;
    this.resValid = false; this.resAddr = -1;   // lr/sc reservation
    this.disp = new Uint8Array(DISP_FB_SIZE);   // memory-mapped framebuffer
    this.dispDirty = true;                       // redraw the canvas on the next render
  }
  loadProgram(asmResult){
    this.mem.fill(0);
    for (const w of asmResult.words) this.view.setUint32(w.pc, w.word, true);
    asmResult.dataBytes.forEach((b, i) => { this.mem[DATA_BASE + i] = b; });
    this.regs.fill(0);
    this.pc = TEXT_BASE;
    this.halted = false; this.haltReason = ''; this.exitCode = null; this.instret = 0;
    this.waitingInput = false;
    this.lastWrites = []; this.lastRegWrite = -1;
    this.resValid = false; this.resAddr = -1;
    this.disp.fill(0); this.dispDirty = true;
  }
  fault(msg){ this.halted = true; this.haltReason = msg; }
  rd(addr, len, signed){
    if (addr >= DISP_FB && addr < DISP_TOP){            // memory-mapped display
      let v = 0;
      if (addr < DISP_CTL)
        for (let k = 0; k < len; k++){ const off = addr - DISP_FB + k; if (off < DISP_FB_SIZE) v |= this.disp[off] << (8 * k); }
      if (signed){ if (len === 1) v = (v << 24) >> 24; else if (len === 2) v = (v << 16) >> 16; }
      return v | 0;
    }
    if (addr < 0 || addr + len > MEM_SIZE){ this.fault(`memory read fault at 0x${(addr>>>0).toString(16)} (pc=0x${this.pc.toString(16)})`); return 0; }
    if (len === 1) return signed ? this.view.getInt8(addr) : this.view.getUint8(addr);
    if (len === 2) return signed ? this.view.getInt16(addr, true) : this.view.getUint16(addr, true);
    return this.view.getInt32(addr, true);
  }
  wr(addr, len, val){
    if (addr >= DISP_FB && addr < DISP_TOP){            // memory-mapped display
      if (addr < DISP_CTL){
        for (let k = 0; k < len; k++){ const off = addr - DISP_FB + k; if (off < DISP_FB_SIZE) this.disp[off] = (val >>> (8 * k)) & 0xFF; }
      } else {
        this.disp.fill(val & 0xFF);                     // control register: flood-fill / clear
      }
      this.dispDirty = true;
      return;
    }
    if (addr < 0 || addr + len > MEM_SIZE){ this.fault(`memory write fault at 0x${(addr>>>0).toString(16)} (pc=0x${this.pc.toString(16)})`); return; }
    if (len === 1) this.view.setUint8(addr, val & 0xFF);
    else if (len === 2) this.view.setUint16(addr, val & 0xFFFF, true);
    else this.view.setInt32(addr, val | 0, true);
    this.lastWrites.push([addr, len]);
  }
  setReg(i, v){ if (i !== 0){ this.regs[i] = v | 0; this.lastRegWrite = i; } }
  readCStr(addr){
    let s = '', a = addr >>> 0, guard = 0;
    while (a < MEM_SIZE && this.mem[a] !== 0 && guard++ < 65536){ s += String.fromCharCode(this.mem[a]); a++; }
    return s;
  }
  ecall(){
    const svc = this.regs[17], a0 = this.regs[10];
    switch (svc){
      case 1:  this.onPrint(String(a0)); break;
      case 4:  this.onPrint(this.readCStr(a0)); break;
      case 5:  this.waitingInput = true; break;   // stall: the ecall retires in provideInput()
      case 11: this.onPrint(String.fromCharCode(a0 & 0xFF)); break;
      case 34: this.onPrint('0x' + (a0 >>> 0).toString(16).padStart(8, '0')); break;
      case 10: this.halted = true; this.haltReason = 'exit'; this.exitCode = 0; break;
      case 93: this.halted = true; this.haltReason = 'exit'; this.exitCode = a0 | 0; break;
      default: this.fault(`unknown ecall service ${svc} (a7) at pc=0x${this.pc.toString(16)}`);
    }
  }
  provideInput(v){
    if (!this.waitingInput) return;
    this.waitingInput = false;
    this.setReg(10, v | 0);
    this.pc = (this.pc + 4) >>> 0;
    this.instret++;
  }
  step(){
    if (this.halted || this.waitingInput) return;
    this.lastWrites = []; this.lastRegWrite = -1;
    const pc = this.pc;
    if (pc < 0 || pc + 4 > MEM_SIZE || (pc & 3)){ this.fault(`instruction fetch fault at 0x${(pc>>>0).toString(16)}`); return; }
    const w = this.view.getUint32(pc, true);
    if (w === 0){ this.fault(`executed a zero word at 0x${pc.toString(16)} (fell off the end of the program?)`); return; }
    const op = w & 0x7F, rdI = (w >> 7) & 0x1F, f3 = (w >> 12) & 7, rs1 = (w >> 15) & 0x1F, rs2 = (w >> 20) & 0x1F, f7 = (w >> 25) & 0x7F;
    const x1 = this.regs[rs1] | 0, x2 = this.regs[rs2] | 0;
    const iImm = (w | 0) >> 20;
    let nextPC = pc + 4;

    switch (op){
      case 0x33: { // R
        let v = 0;
        if (f7 === 1){ // M extension
          if (!this.isaM){ this.fault(`M-extension instruction at 0x${pc.toString(16)} but the ISA is RV32I`); return; }
          switch (f3){
            case 0: v = Math.imul(x1, x2); break;
            case 1: v = Number((BigInt(x1) * BigInt(x2)) >> 32n) | 0; break;
            case 2: v = Number((BigInt(x1) * BigInt(x2 >>> 0)) >> 32n) | 0; break;
            case 3: v = Number((BigInt(x1 >>> 0) * BigInt(x2 >>> 0)) >> 32n) | 0; break;
            case 4: v = x2 === 0 ? -1 : (x1 === -2147483648 && x2 === -1 ? -2147483648 : (x1 / x2) | 0); break;
            case 5: v = x2 === 0 ? -1 : Math.floor((x1 >>> 0) / (x2 >>> 0)) | 0; break;
            case 6: v = x2 === 0 ? x1 : (x1 === -2147483648 && x2 === -1 ? 0 : x1 % x2); break;
            case 7: v = x2 === 0 ? x1 : ((x1 >>> 0) % (x2 >>> 0)) | 0; break;
          }
        } else {
          switch (f3){
            case 0: v = f7 === 0x20 ? (x1 - x2) | 0 : (x1 + x2) | 0; break;
            case 1: v = x1 << (x2 & 31); break;
            case 2: v = x1 < x2 ? 1 : 0; break;
            case 3: v = (x1 >>> 0) < (x2 >>> 0) ? 1 : 0; break;
            case 4: v = x1 ^ x2; break;
            case 5: v = f7 === 0x20 ? x1 >> (x2 & 31) : x1 >>> (x2 & 31); break;
            case 6: v = x1 | x2; break;
            case 7: v = x1 & x2; break;
          }
        }
        this.setReg(rdI, v); break;
      }
      case 0x13: { // I ALU
        let v = 0;
        switch (f3){
          case 0: v = (x1 + iImm) | 0; break;
          case 1: v = x1 << (rs2 & 31); break;
          case 2: v = x1 < iImm ? 1 : 0; break;
          case 3: v = (x1 >>> 0) < (iImm >>> 0) ? 1 : 0; break;
          case 4: v = x1 ^ iImm; break;
          case 5: v = f7 === 0x20 ? x1 >> (rs2 & 31) : x1 >>> (rs2 & 31); break;
          case 6: v = x1 | iImm; break;
          case 7: v = x1 & iImm; break;
        }
        this.setReg(rdI, v); break;
      }
      case 0x03: { // loads
        const a = (x1 + iImm) | 0;
        let v;
        switch (f3){
          case 0: v = this.rd(a, 1, true); break;
          case 1: v = this.rd(a, 2, true); break;
          case 2: v = this.rd(a, 4, true); break;
          case 4: v = this.rd(a, 1, false); break;
          case 5: v = this.rd(a, 2, false); break;
          default: this.fault(`illegal load funct3=${f3} at 0x${pc.toString(16)}`); return;
        }
        if (this.halted) return;
        this.setReg(rdI, v); break;
      }
      case 0x23: { // stores
        const sImm = ((w >> 7) & 0x1F) | (((w | 0) >> 25) << 5);
        const a = (x1 + sImm) | 0;
        if (f3 > 2){ this.fault(`illegal store funct3=${f3} at 0x${pc.toString(16)}`); return; }
        this.wr(a, f3 === 0 ? 1 : f3 === 1 ? 2 : 4, x2);
        if (this.halted) return;
        break;
      }
      case 0x63: { // branches
        const bImm = (((w >> 8) & 0xF) << 1) | (((w >> 25) & 0x3F) << 5) | (((w >> 7) & 1) << 11) | ((((w | 0) >> 31)) << 12);
        let take = false;
        switch (f3){
          case 0: take = x1 === x2; break;
          case 1: take = x1 !== x2; break;
          case 4: take = x1 < x2; break;
          case 5: take = x1 >= x2; break;
          case 6: take = (x1 >>> 0) < (x2 >>> 0); break;
          case 7: take = (x1 >>> 0) >= (x2 >>> 0); break;
          default: this.fault(`illegal branch funct3=${f3}`); return;
        }
        if (take) nextPC = (pc + bImm) | 0;
        break;
      }
      case 0x2F: { // A extension (single hart: lr/sc via a reservation flag)
        if (!this.isaA){ this.fault(`A-extension instruction at 0x${pc.toString(16)} but the A extension is disabled`); return; }
        if (f3 !== 2){ this.fault(`illegal atomic funct3=${f3} at 0x${pc.toString(16)}`); return; }
        const f5 = (w >>> 27) & 0x1F;
        const a = x1 | 0;
        if (a & 3){ this.fault(`misaligned atomic access at 0x${(a>>>0).toString(16)} (pc=0x${pc.toString(16)})`); return; }
        if (f5 === 0x02){           // lr.w
          const v = this.rd(a, 4, true);
          if (this.halted) return;
          this.resValid = true; this.resAddr = a;
          this.setReg(rdI, v);
        } else if (f5 === 0x03){    // sc.w
          if (this.resValid && this.resAddr === a){
            this.wr(a, 4, x2);
            if (this.halted) return;
            this.setReg(rdI, 0);
          } else this.setReg(rdI, 1);
          this.resValid = false;
        } else {                    // amo*.w: rd = old, mem = old OP rs2
          const old = this.rd(a, 4, true);
          if (this.halted) return;
          let nv;
          switch (f5){
            case 0x00: nv = (old + x2) | 0; break;
            case 0x01: nv = x2; break;
            case 0x04: nv = old ^ x2; break;
            case 0x08: nv = old | x2; break;
            case 0x0C: nv = old & x2; break;
            case 0x10: nv = Math.min(old, x2); break;
            case 0x14: nv = Math.max(old, x2); break;
            case 0x18: nv = (old >>> 0) < (x2 >>> 0) ? old : x2; break;
            case 0x1C: nv = (old >>> 0) > (x2 >>> 0) ? old : x2; break;
            default: this.fault(`illegal atomic funct5=${f5} at 0x${pc.toString(16)}`); return;
          }
          this.wr(a, 4, nv);
          if (this.halted) return;
          this.setReg(rdI, old);
        }
        break;
      }
      case 0x37: this.setReg(rdI, w & 0xFFFFF000); break;       // lui
      case 0x17: this.setReg(rdI, (pc + (w & 0xFFFFF000)) | 0); break; // auipc
      case 0x6F: { // jal
        const j = (((w >> 21) & 0x3FF) << 1) | (((w >> 20) & 1) << 11) | (((w >> 12) & 0xFF) << 12) | ((((w | 0) >> 31)) << 20);
        this.setReg(rdI, pc + 4);
        nextPC = (pc + j) | 0;
        break;
      }
      case 0x67: { // jalr
        const t = (x1 + iImm) & ~1;
        this.setReg(rdI, pc + 4);
        nextPC = t;
        break;
      }
      case 0x73:
        if (iImm === 1){ this.fault(`ebreak at 0x${pc.toString(16)}`); return; }
        this.ecall();
        if (this.halted || this.waitingInput) return;   // a waiting ecall retires in provideInput()
        break;
      default:
        this.fault(`illegal instruction 0x${w.toString(16).padStart(8,'0')} at 0x${pc.toString(16)}`);
        return;
    }
    this.pc = nextPC >>> 0;
    this.instret++;
  }
}

// ---------------- Node.js export (for the test suite) ----------------
if (typeof module !== 'undefined' && module.exports){
  module.exports = { tokenize, parse, codegen, compileC, assemble, disasm, CPU,
    TEXT_BASE, DATA_BASE, MEM_SIZE, DISP_W, DISP_H, DISP_FB, DISP_FB_SIZE, DISP_CTL,
    REG_NAMES, ABI };
}
