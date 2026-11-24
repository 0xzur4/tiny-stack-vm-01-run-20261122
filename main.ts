// Interpreter for make.fun's tiny stack ISA v1 (32-bit wrapping ints,
// with their own exit codes, step/output limits). Node 22, stdlib only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode: pops in the high nibble, pushes in the low; 0 is invalid or no-op.
const Q = new Uint8Array(256);
Q[0x01] = 0x01; Q[0x02] = 0x01; Q[0x52] = 0x01;
Q[0x03] = 0x10; Q[0x04] = 0x12; Q[0x05] = 0x22; Q[0x06] = 0x23; Q[0x07] = 0x33;
Q[0x31] = 0x10; Q[0x32] = 0x10; Q[0x40] = 0x11; Q[0x41] = 0x20;
Q[0x50] = 0x10; Q[0x51] = 0x10; Q[0x53] = 0x10;
for (let o = 0x10; o <= 0x16; o++) Q[o] = 0x21;
for (let o = 0x18; o <= 0x1e; o++) Q[o] = 0x21;
for (let o = 0x20; o <= 0x22; o++) Q[o] = 0x21;
// NEG/NOT are unary: set after the 0x18..0x1e loop, which would overwrite NOT.
Q[0x17] = 0x11; Q[0x1b] = 0x11;

function run(p: Uint8Array, inp: Uint8Array) {
  const S = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const end = (code: number) => ({ out: out.slice(0, ol), code });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc];
    if (op !== 0x00 && op !== 0x30 && op !== 0x33 && op !== 0x34 && Q[op] === 0) return end(5);
    const imm = op === 0x01 ? 1 : op === 0x02 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= p.length) return end(9);
    steps++;
    const q = Q[op];
    const pops = q >> 4;
    if (sp < pops) return end(2);
    if (sp - pops + (q & 15) > 256) return end(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        S[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        S[sp] = S[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = S[sp - 1];
        S[sp - 1] = S[sp - 2];
        S[sp - 2] = t;
        break;
      }
      case 0x06:
        S[sp] = S[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = S[sp - 3];
        S[sp - 3] = S[sp - 2];
        S[sp - 2] = S[sp - 1];
        S[sp - 1] = a;
        break;
      }
      case 0x17:
        S[sp - 1] = -S[sp - 1] | 0;
        break;
      case 0x1b:
        S[sp - 1] = ~S[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1];
        const a = S[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = S[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = S[sp - 1];
        const v = S[sp - 2];
        if (addr < 0 || addr >= 256) return end(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = S[--sp] & 255;
        break;
      case 0x52:
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(S[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
