// A tiny stack virtual machine for make.fun's tiny-stack-vm-01 bounty: an interpreter for
// the tiny stack ISA (wrapping 32-bit integers, 256-value stack, 64-deep calls, 256 words
// of memory, byte input and output, ten traps, step and output limits), plus its driver.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// (opcode, immediate bytes, pops, pushes) in fours; an immediate of -1 marks no opcode.
const IMM = new Int8Array(256).fill(-1);
const POPS = new Int8Array(256);
const PUSHES = new Int8Array(256);
const T = ('0 0 0 0 1 1 0 1 2 4 0 1 3 0 1 0 4 0 1 2 5 0 2 2 6 0 2 3 7 0 3 3 ' +
  '16 0 2 1 17 0 2 1 18 0 2 1 19 0 2 1 20 0 2 1 21 0 2 1 22 0 2 1 23 0 1 1 ' +
  '24 0 2 1 25 0 2 1 26 0 2 1 27 0 1 1 28 0 2 1 29 0 2 1 30 0 2 1 32 0 2 1 ' +
  '33 0 2 1 34 0 2 1 48 2 0 0 49 2 1 0 50 2 1 0 51 2 0 0 52 0 0 0 64 0 1 1 ' +
  '65 0 2 0 80 0 1 0 81 0 1 0 82 0 0 1 83 0 1 0').split(' ').map(Number);
for (let i = 0; i < T.length; i += 4) {
  IMM[T[i]] = T[i + 1];
  POPS[T[i]] = T[i + 2];
  PUSHES[T[i]] = T[i + 3];
}

// Runs one program on its input to its end; returns its output bytes and exit code.
function run(prog, input) {
  const n = prog.length;
  const S = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65_536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const end = (code) => ({ bytes: out.subarray(0, olen), code });

  for (;;) {
    // One step, checks in the ISA's order.
    if (steps === 1_000_000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return end(5);
    if (pc + imm >= n) return end(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < POPS[op]) return end(2);
    if (sp - POPS[op] + PUSHES[op] > 256) return end(3);
    pc = next;

    // Two-operand arithmetic and comparisons: b is the top, a below it; push the result.
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = S[sp - 1];
      const a = S[sp - 2];
      if (op >= 0x13 && op <= 0x16 && b === 0) return end(4);
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) r = a === -2147483648 && b === -1 ? a : (a / b) | 0; // INT_MIN / -1
      else if (op === 0x14) r = b === -1 ? 0 : (a % b) | 0; // x % -1 is 0; else a's sign
      else if (op === 0x15) r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      else if (op === 0x16) r = ((a >>> 0) % (b >>> 0)) | 0;
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31); // arithmetic
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      S[--sp - 1] = r;
      continue;
    }

    switch (op) {
      case 0x00:
        return end(0);
      case 0x01: // PUSH8, sign-extended
        S[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        S[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        S[sp] = S[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = S[sp - 1];
        S[sp - 1] = S[sp - 2];
        S[sp - 2] = t;
        break;
      }
      case 0x06:
        S[sp] = S[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = S[sp - 3];
        S[sp - 3] = S[sp - 2];
        S[sp - 2] = S[sp - 1];
        S[sp - 1] = a;
        break;
      }
      case 0x17: // NEG: -(-2147483648) is -2147483648
        S[sp - 1] = -S[sp - 1] | 0;
        break;
      case 0x1b:
        S[sp - 1] = ~S[sp - 1];
        break;
      case 0x30: // Jumps: target = the next address + the signed offset
      case 0x31:
      case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: an unsigned absolute address
        if (csp === 64) return end(7);
        C[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = S[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = S[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        M[addr] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal; past the output limit, writes nothing
        const s = String(S[sp - 1]);
        if (olen + s.length > 65_536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen + i] = s.charCodeAt(i);
        olen += s.length;
        break;
      }
      case 0x51: // PUTC: the value's low byte
        if (olen + 1 > 65_536) return end(11);
        out[olen++] = S[--sp] & 255;
        break;
      case 0x52: // IN: the next input byte, else -1
        S[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53: // EXIT: the value's low byte
        return end(S[--sp] & 255);
    }
  }
}

// The driver: answer every instance of the set in one run.
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const prog = readFileSync(join(I, id, 'program.bin'));
  const input = readFileSync(join(I, id, 'input.bin'));
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
