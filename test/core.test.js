'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const { compileC, assemble, disasm, CPU, DATA_BASE, DISP_FB, DISP_CTL, DISP_FB_SIZE } =
  require('../core.js');

// ---------- helpers ----------
function makeCPU(res, isa = 'IMA'){
  const cpu = new CPU();
  cpu.isaM = isa.includes('M');
  cpu.isaA = isa.includes('A');
  let out = '';
  cpu.onPrint = s => { out += s; };
  cpu.getOut = () => out;
  cpu.loadProgram(res);
  return cpu;
}
function runToHalt(cpu, { inputs = [], maxSteps = 5e6 } = {}){
  let steps = 0;
  while (!cpu.halted && steps++ < maxSteps){
    cpu.step();
    if (cpu.waitingInput){
      if (!inputs.length) throw new Error('program asked for input but the test provided none');
      cpu.provideInput(inputs.shift());
    }
  }
  if (!cpu.halted) throw new Error(`did not halt within ${maxSteps} steps`);
  return cpu;
}
function runC(src, opts = {}){
  const res = assemble(compileC(src), opts.isa || 'IMA');
  const cpu = runToHalt(makeCPU(res, opts.isa || 'IMA'), opts);
  return { out: cpu.getOut(), exit: cpu.exitCode, cpu };
}
function runAsm(src, opts = {}){
  const res = assemble(src, opts.isa || 'IMA');
  const cpu = runToHalt(makeCPU(res, opts.isa || 'IMA'), opts);
  return { out: cpu.getOut(), exit: cpu.exitCode, cpu, res };
}
// wraps a bare instruction sequence with an exit
function asmMain(body){
  return `.text\n_start:\n${body}\n  li a0, 0\n  li a7, 93\n  ecall\n`;
}
function word0(src){ return assemble(src).words[0].word >>> 0; }

// ---------- C compiler: language features ----------
test('print_str and string escapes', () => {
  const r = runC(`int main(){ print_str("hi\\tthere\\n"); return 0; }`);
  assert.equal(r.out, 'hi\tthere\n');
  assert.equal(r.exit, 0);
});

test('arithmetic precedence and parentheses', () => {
  const r = runC(`int main(){ print_int(2 + 3 * 4); print_char(' '); print_int((2 + 3) * 4); return 0; }`);
  assert.equal(r.out, '14 20');
});

test('signed division and remainder truncate toward zero', () => {
  const r = runC(`int main(){
    print_int(-7 / 2); print_char(' '); print_int(-7 % 2);
    print_char(' '); print_int(7 / -2); return 0; }`);
  assert.equal(r.out, '-3 -1 -3');
});

test('pointers: address-of, dereference, pointer arithmetic', () => {
  const r = runC(`int main(){
    int a[3]; int *p = &a[0];
    *p = 10; *(p + 1) = 20; p[2] = 30;
    print_int(a[0] + a[1] + a[2]);
    print_char(' ');
    print_int(&a[2] - &a[0]);
    return 0; }`);
  assert.equal(r.out, '60 2');
});

test('char type, strings are byte pointers', () => {
  const r = runC(`int main(){ char *s = "AB"; print_int(s[0]); print_char(s[1]); return 0; }`);
  assert.equal(r.out, '65B');
});

test('global scalars and arrays with initialisers', () => {
  const r = runC(`
    int g = 41;
    int tab[4] = {1, 2, 3};
    char c;
    int main(){ c = 1; print_int(g + tab[0] + tab[1] + tab[2] + tab[3] + c); return 0; }`);
  assert.equal(r.out, '48');
});

test('recursion: fib(10)', () => {
  const r = runC(`
    int fib(int n){ if (n < 2) return n; return fib(n-1) + fib(n-2); }
    int main(){ print_int(fib(10)); return 0; }`);
  assert.equal(r.out, '55');
});

test('while, for, break, continue', () => {
  const r = runC(`int main(){
    int s = 0;
    for (int i = 0; i < 10; i++){
      if (i == 3) continue;
      if (i == 7) break;
      s += i;
    }
    int j = 0;
    while (1){ j++; if (j == 5) break; }
    print_int(s); print_char(' '); print_int(j);
    return 0; }`);
  assert.equal(r.out, '18 5');
});

test('ternary, logical ops short-circuit', () => {
  const r = runC(`
    int calls = 0;
    int bump(){ calls++; return 1; }
    int main(){
      int a = 0 && bump();
      int b = 1 || bump();
      print_int(calls); print_char(' ');
      print_int(a ? 100 : (b ? 42 : 7));
      return 0; }`);
  assert.equal(r.out, '0 42');
});

test('compound assignment and increment/decrement', () => {
  const r = runC(`int main(){
    int x = 10;
    x += 5; x <<= 1; x /= 3;
    int y = x++;
    int z = ++x;
    print_int(x); print_char(' '); print_int(y); print_char(' '); print_int(z);
    return 0; }`);
  assert.equal(r.out, '12 10 12');
});

test('sizeof', () => {
  const r = runC(`int main(){
    int a[6]; char b[3];
    print_int(sizeof(int)); print_int(sizeof(char)); print_int(sizeof(int*));
    print_int(sizeof a); print_int(sizeof b);
    return 0; }`);
  assert.equal(r.out, '414243');     // 4,1,4,24,3 concatenated
});

test('eight function arguments', () => {
  const r = runC(`
    int sum8(int a, int b, int c, int d, int e, int f, int g, int h){
      return a + b + c + d + e + f + g + h;
    }
    int main(){ print_int(sum8(1,2,3,4,5,6,7,8)); return 0; }`);
  assert.equal(r.out, '36');
});

test('main return value becomes the exit code', () => {
  assert.equal(runC(`int main(){ return 42; }`).exit, 42);
});

test('read_int stalls the CPU and provideInput resumes it', () => {
  const res = assemble(compileC(`int main(){ int x = read_int(); print_int(x * 2); return 0; }`));
  const cpu = makeCPU(res);
  let guard = 0;
  while (!cpu.waitingInput && guard++ < 10000) cpu.step();
  assert.equal(cpu.waitingInput, true);
  assert.equal(cpu.halted, false);
  const pcAtStall = cpu.pc;
  cpu.step();                                  // stepping while stalled is a no-op
  assert.equal(cpu.pc, pcAtStall);
  cpu.provideInput(21);
  runToHalt(cpu);
  assert.equal(cpu.getOut(), '42');
});

test('compile errors carry a C line number', () => {
  assert.throws(() => compileC(`int main(){\n  y = 1;\n  return 0;\n}`),
    e => e.isCompile && e.cline === 2 && /not declared/.test(e.message));
  assert.throws(() => compileC(`int f(){ return 1; }`), e => /no main/.test(e.message));
});

// ---------- assembler: encodings ----------
test('known instruction encodings', () => {
  assert.equal(word0('.text\naddi ra, zero, 5'), 0x00500093);
  assert.equal(word0('.text\nadd a0, a1, a2'), 0x00c58533);
  assert.equal(word0('.text\nsub s0, s1, s2'), 0x41248433);
  assert.equal(word0('.text\nlui a0, 0xdead'), 0x0dead537);
  assert.equal(word0('.text\nlw a0, 8(sp)'), 0x00812503);
  assert.equal(word0('.text\nsw a0, -4(s0)'), 0xfea42e23);
  assert.equal(word0('.text\necall'), 0x00000073);
  assert.equal(word0('.text\nmul a0, a0, a1'), 0x02b50533);
  assert.equal(word0('.text\namoadd.w t0, s3, (s1)'), 0x0134a2af);
  assert.equal(word0('.text\nlr.w t0, (s1)'), 0x1004a2af);
});

test('branch and jump offsets resolve labels in both directions', () => {
  const res = assemble('.text\n_start:\n  nop\n  beq zero, zero, _start\n  jal end\nend:\n  nop');
  assert.equal(disasm(res.words[1].word, 4), 'beq zero, zero, 0x0');
  assert.equal(disasm(res.words[2].word, 8), 'jal ra, 0xc');
});

test('li expands to one or two instructions by immediate size', () => {
  assert.equal(assemble('.text\nli a0, 100').words.length, 1);
  const big = assemble('.text\nli a0, 0x12345');
  assert.equal(big.words.length, 2);
  const cpu = makeCPU(assemble(asmMain('  li a0, 0x12345\n  mv s2, a0')));
  runToHalt(cpu);
  assert.equal(cpu.regs[18], 0x12345);
});

test('.word accepts labels (address tables)', () => {
  const src = asmMain('  la t0, table\n  lw s2, 0(t0)\n  lw s3, 4(t0)') +
    '.data\nvalue: .word 77\ntable: .word value, 0x123\n';
  const { cpu, res } = runAsm(src);
  assert.equal(cpu.regs[18], res.symbols.get('value'));
  assert.equal(cpu.regs[19], 0x123);
});

test('.word with an unknown label is an error', () => {
  assert.throws(() => assemble('.data\nx: .word nowhere'), e => e.isAsm && /nowhere/.test(e.message));
});

test('.half, .space, and .align lay out data correctly', () => {
  const res = assemble('.data\na: .byte 1\n.align 2\nb: .word 7\nc: .half 0x1234\n.align 2\nd: .space 5\ne: .byte 9');
  const sym = res.symbols;
  assert.equal(sym.get('a'), DATA_BASE);
  assert.equal(sym.get('b'), DATA_BASE + 4);        // aligned past the padding
  assert.equal(sym.get('c'), DATA_BASE + 8);
  assert.equal(sym.get('d'), DATA_BASE + 12);       // re-aligned after the half
  assert.equal(sym.get('e'), DATA_BASE + 17);
  assert.deepEqual(res.dataBytes.slice(8, 10), [0x34, 0x12]);   // little-endian half
});

test('.asciiz appends a NUL and honours escapes', () => {
  const res = assemble('.data\ns: .asciiz "a\\tb"');
  assert.deepEqual(res.dataBytes, [0x61, 9, 0x62, 0]);
});

test('assembler errors: unknown mnemonic, range checks, duplicate labels', () => {
  assert.throws(() => assemble('.text\nfoo a0, a1'), /unknown instruction/);
  assert.throws(() => assemble('.text\naddi a0, a0, 5000'), /12 bits/);
  assert.throws(() => assemble('.text\nx:\nx:\n  nop'), /defined twice/);
  assert.throws(() => assemble('.text\nlw a0, 5000(sp)'), /out of range/);
});

test('ISA gating: M and A instructions rejected when the extension is off', () => {
  assert.throws(() => assemble('.text\nmul a0, a0, a1', 'I'), /requires the M extension/);
  assert.throws(() => assemble('.text\namoadd.w a0, a1, (a2)', 'IM'), /requires the A extension/);
  assert.doesNotThrow(() => assemble('.text\nmul a0, a0, a1', 'IM'));
});

test('disassembler formats common instructions', () => {
  assert.equal(disasm(0x00500093, 0), 'addi ra, zero, 5');
  assert.equal(disasm(0x00812503, 0), 'lw a0, 8(sp)');
  assert.equal(disasm(0x00000073, 0), 'ecall');
  assert.equal(disasm(0x0134a2af, 0), 'amoadd.w t0, s3, (s1)');
});

// ---------- CPU semantics ----------
test('RV32M division edge cases match the spec', () => {
  const body = `
  li t0, 7
  li t1, 0
  div s2, t0, t1          # /0 -> -1
  rem s3, t0, t1          # %0 -> dividend
  li t2, -2147483648
  li t3, -1
  div s4, t2, t3          # overflow -> INT_MIN
  rem s5, t2, t3          # overflow -> 0
  divu s6, t3, t0         # unsigned: 0xFFFFFFFF / 7`;
  const { cpu } = runAsm(asmMain(body));
  assert.equal(cpu.regs[18], -1);
  assert.equal(cpu.regs[19], 7);
  assert.equal(cpu.regs[20], -2147483648);
  assert.equal(cpu.regs[21], 0);
  assert.equal(cpu.regs[22], Math.floor(0xFFFFFFFF / 7) | 0);
});

test('mulh / mulhu high halves', () => {
  const body = `
  li t0, 0x40000000
  li t1, 8
  mulh  s2, t0, t1        # (2^30 * 8) >> 32 = 2
  li t2, -1
  mulhu s3, t2, t2        # (2^32-1)^2 >> 32 = 0xFFFFFFFE`;
  const { cpu } = runAsm(asmMain(body));
  assert.equal(cpu.regs[18], 2);
  assert.equal(cpu.regs[19] >>> 0, 0xFFFFFFFE);
});

test('sra vs srl, slt vs sltu', () => {
  const body = `
  li t0, -8
  srai s2, t0, 1
  srli s3, t0, 28
  li t1, 1
  slt  s4, t0, t1         # signed: -8 < 1
  sltu s5, t0, t1         # unsigned: 0xFFFFFFF8 < 1 is false`;
  const { cpu } = runAsm(asmMain(body));
  assert.equal(cpu.regs[18], -4);
  assert.equal(cpu.regs[19], 0xF);
  assert.equal(cpu.regs[20], 1);
  assert.equal(cpu.regs[21], 0);
});

test('x0 is hard-wired to zero', () => {
  const { cpu } = runAsm(asmMain('  li t0, 99\n  add zero, t0, t0'));
  assert.equal(cpu.regs[0], 0);
});

test('lr/sc: success, then failure without a reservation', () => {
  const body = `
  la s1, cell
  lr.w t0, (s1)
  li t1, 5
  sc.w s2, t1, (s1)       # succeeds: 0
  li t2, 9
  sc.w s3, t2, (s1)       # no reservation: 1
  lw s4, 0(s1)`;
  const { cpu } = runAsm(asmMain(body) + '.data\ncell: .word 1\n');
  assert.equal(cpu.regs[18], 0);
  assert.equal(cpu.regs[19], 1);
  assert.equal(cpu.regs[20], 5);
});

test('amoadd returns the old value and updates memory', () => {
  const body = `
  la s1, cell
  li t0, 10
  amoadd.w s2, t0, (s1)
  lw s3, 0(s1)`;
  const { cpu } = runAsm(asmMain(body) + '.data\ncell: .word 32\n');
  assert.equal(cpu.regs[18], 32);
  assert.equal(cpu.regs[19], 42);
});

test('misaligned atomics fault', () => {
  const { cpu } = runAsm(asmMain('  li s1, 0x4001\n  lr.w t0, (s1)'));
  assert.match(cpu.haltReason, /misaligned atomic/);
});

test('out-of-range memory access faults', () => {
  const r1 = runAsm(asmMain('  li t0, 0x20000\n  lw t1, 0(t0)'));
  assert.match(r1.cpu.haltReason, /read fault/);
  const r2 = runAsm(asmMain('  li t0, -64\n  sw t0, 0(t0)'));
  assert.match(r2.cpu.haltReason, /write fault/);
});

test('executing a zero word and ebreak both fault with a message', () => {
  const z = runAsm('.text\n_start:\n  nop');   // falls off the end
  assert.match(z.cpu.haltReason, /zero word/);
  const b = runAsm(asmMain('  ebreak'));
  assert.match(b.cpu.haltReason, /ebreak/);
});

test('exit ecall (93) sets the exit code', () => {
  const { exit } = runAsm('.text\n_start:\n  li a0, 7\n  li a7, 93\n  ecall');
  assert.equal(exit, 7);
});

// ---------- memory-mapped display ----------
test('framebuffer bytes land in the display, not RAM', () => {
  const body = `
  li t0, ${DISP_FB}
  li t1, 0xE0
  sb t1, 0(t0)            # pixel 0 = red
  lb s2, 0(t0)            # reads back (sign-extended)`;
  const { cpu } = runAsm(asmMain(body));
  assert.equal(cpu.disp[0], 0xE0);
  assert.equal(cpu.regs[18], (0xE0 << 24) >> 24);
});

test('control register flood-fills the framebuffer', () => {
  const body = `
  li t0, ${DISP_CTL}
  li t1, 0x1C
  sw t1, 0(t0)`;
  const { cpu } = runAsm(asmMain(body));
  assert.equal(cpu.disp[0], 0x1C);
  assert.equal(cpu.disp[DISP_FB_SIZE - 1], 0x1C);
  assert.ok(cpu.dispDirty);
});

test('word stores span the framebuffer correctly', () => {
  const body = `
  li t0, ${DISP_FB}
  li t1, 0x04030201
  sw t1, 0(t0)`;
  const { cpu } = runAsm(asmMain(body));
  assert.deepEqual(Array.from(cpu.disp.slice(0, 4)), [1, 2, 3, 4]);
});
