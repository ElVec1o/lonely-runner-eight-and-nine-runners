// gen_prime13.rs : per-prime generator of the Lean modules of the nine-runner cover tree (one prime p of the set S36 per run).
// Cover tree (K=8, levels p, 3p, 9p, branching on the uncovered time with fewest allowed coverers,
// children increasing); this program (a) state kept as the masks the Lean checker uses, (b) bound leaves carry an E8-style hint
// (threshold t, exception set T) with the uniform top-r bound, (c) output is Lean source (tables, packed certificates).
// Exact integer/bitmask arithmetic only.
// usage: gen_prime13 P OUTDIR LIM CHUNK 1 120 120 40 40 16 40 emit   (P prime, LIM and CHUNK from inputs/PARAMS.tsv; last word: emit, or stats for a dry run)
use std::fmt::Write as FW;
use std::fs;

const MW: usize = 36;
type B = [u64; MW];
const Z: B = [0; MW];
const K: usize = 8;

fn pc(a: &B) -> usize { a.iter().map(|x| x.count_ones() as usize).sum() }
fn and(a: &B, b: &B) -> B { let mut r = Z; for i in 0..MW { r[i] = a[i] & b[i]; } r }
fn andn(a: &B, b: &B) -> B { let mut r = Z; for i in 0..MW { r[i] = a[i] & !b[i]; } r }
fn or(a: &B, b: &B) -> B { let mut r = Z; for i in 0..MW { r[i] = a[i] | b[i]; } r }
fn tb(a: &B, x: usize) -> bool { (a[(x - 1) >> 6] >> ((x - 1) & 63)) & 1 == 1 }
fn sb(a: &mut B, x: usize) { a[(x - 1) >> 6] |= 1u64 << ((x - 1) & 63); }
fn bits(a: &B) -> Vec<usize> {
    let mut v = Vec::new();
    for w in 0..MW { let mut x = a[w]; while x != 0 { v.push(w * 64 + x.trailing_zeros() as usize + 1); x &= x - 1; } }
    v
}
fn is_zero(a: &B) -> bool { a.iter().all(|&x| x == 0) }

struct Level { m: usize, n: usize, cov: Vec<B>, adm: B, full: B, m3: B, lowp: B, lowt: B, pcls: Vec<B>, tcls: Vec<B> }

fn build_level(p: usize, l: usize) -> Level {
    let m = l * p; let n = m / 2; assert!(m % 2 == 1 && n <= 64 * MW);
    let mut cov = vec![Z; n + 1];
    for x in 1..=n { for t in 1..=n {
        let r = (x * t) % m; let d = r.min(m - r);
        if (K + 1) * d < m { sb(&mut cov[x], t); }
    } }
    let (mut adm, mut full, mut m3, mut lowp, mut lowt) = (Z, Z, Z, Z, Z);
    for x in 1..=n {
        sb(&mut full, x); if x % p != 0 { sb(&mut adm, x); } if x % 3 == 0 && l > 1 { sb(&mut m3, x); }
        if x <= (p - 1) / 2 { sb(&mut lowp, x); } if x <= (3 * p - 1) / 2 { sb(&mut lowt, x); }
    }
    let mut pcls = vec![Z; n + 1]; let mut tcls = vec![Z; n + 1];
    for x in 1..=n {
        for y in 1..=n {
            let (a, b) = (x % p, y % p); if a == b || a + b == p { sb(&mut pcls[x], y); }
            let (a, b) = (x % (3 * p), y % (3 * p)); if a == b || a + b == 3 * p { sb(&mut tcls[x], y); }
        }
    }
    Level { m, n, cov, adm, full, m3, lowp, lowt, pcls, tcls }
}

#[derive(Clone)]
struct S { unc: B, av: B, fr: usize, r: usize, c3: usize, ch: B, im: B, it: B, mp: B, mq: B, mf: B }

// ---------- Lean literal emitters ----------
fn hexw(w: &[u64]) -> String {
    let mut i = w.len(); while i > 0 && w[i - 1] == 0 { i -= 1; }
    if i == 0 { return "(nat_lit 0)".into(); }
    let mut s = format!("(nat_lit 0x{:x}", w[i - 1]); for x in w[..i - 1].iter().rev() { write!(s, "{:016x}", x).unwrap(); } s.push(')'); s
}
fn spread_lit(a: &B) -> String { // class x -> bit 16x
    let mx = bits(a).into_iter().max().unwrap_or(0); let mut o = vec![0u64; (16 * (mx + 1) + 63) / 64];
    for x in bits(a) { let b = 16 * x; o[b / 64] |= 1u64 << (b % 64); } hexw(&o)
}
fn spread_lit_with0(a: &B, n: usize) -> String { // fields 0..n all set (the `ones` mask)
    let _ = a; let mut o = vec![0u64; (16 * (n + 1) + 63) / 64]; for x in 0..=n { let b = 16 * x; o[b / 64] |= 1u64 << (b % 64); } hexw(&o)
}
fn compact_lit(a: &B) -> String { // time t -> bit t
    let mx = bits(a).into_iter().max().unwrap_or(0); let mut o = vec![0u64; (mx + 1 + 63) / 64 + 1];
    for t in bits(a) { o[t / 64] |= 1u64 << (t % 64); } hexw(&o)
}
fn pow2_16(c: usize) -> String { let nh = 4 * c; let mut s = String::from("(nat_lit 0x1"); for _ in 0..nh { s.push('0'); } s.push(')'); s }
fn pow2_lit(e: usize) -> String { let mut o = vec![0u64; e / 64 + 1]; o[e / 64] |= 1u64 << (e % 64); hexw(&o) }
fn maskrange_lit(lo: usize, hi: usize) -> String { let mut o = vec![0u64; hi / 64 + 1]; for t in lo..hi { o[t / 64] |= 1u64 << (t % 64); } hexw(&o) }
fn nat16(f: &[u16], chunk: usize) -> Vec<String> { // chunk fields per Nat
    let mut out = vec![]; let mut i = 0;
    while i < f.len() || i == 0 {
        let e = (i + chunk).min(f.len()); let mut w = vec![0u64; (chunk * 16 + 63) / 64];
        for (k, x) in f[i..e].iter().enumerate() { let b = 16 * k; w[b / 64] |= (*x as u64) << (b % 64); }
        out.push(hexw(&w)); i += chunk; if f.is_empty() { break; }
    }
    out
}


// ---------- packed tables and cfRef contexts ----------
fn words_bits(bitsv: &[usize], stride: usize, nwords: usize) -> Vec<u64> {
    let mut o = vec![0u64; nwords];
    for &x in bitsv { let b = stride * x; o[b / 64] |= 1u64 << (b % 64); }
    o
}

// pack entries (each at most w bits) g per blob; blob = sum_k entry_k << (w k); hex literals
fn pack_blobs(entries: &[Vec<u64>], w: usize, g: usize) -> Vec<String> {
    let nb = (entries.len() + g - 1) / g; let nw = (g * w + 63) / 64 + 2;
    let mut out = vec![];
    for b in 0..nb {
        let mut o = vec![0u64; nw];
        for k in 0..g {
            let idx = b * g + k; if idx >= entries.len() { break; }
            let off = w * k;
            for (wi, &word) in entries[idx].iter().enumerate() {
                if word == 0 { continue; }
                let bit = off + 64 * wi; let (q, r) = (bit / 64, bit % 64);
                o[q] |= word << r; if r != 0 { o[q + 1] |= word >> (64 - r); }
            }
        }
        out.push(hexw(&o));
    }
    out
}

fn emit_table(s: &mut String, name: &str, entries: &[Vec<u64>], w: usize, g: usize) {
    let bl = pack_blobs(entries, w, g);
    for (i, b) in bl.iter().enumerate() { writeln!(s, "def {}_B{} : Nat := {}", name, i, b).unwrap(); }
    fn tr(s: &mut String, name: &str, lo: usize, hi: usize) -> String {
        let nm = format!("{}_T{}_{}", name, lo, hi);
        if hi - lo == 1 { writeln!(s, "def {} (_ : Nat) : Nat := {}_B{}", nm, name, lo).unwrap(); return nm; }
        let mid = (lo + hi) / 2; let a = tr(s, name, lo, mid); let b = tr(s, name, mid, hi);
        writeln!(s, "def {} (i : Nat) : Nat := bif Nat.ble (nat_lit {}) i then {} i else {} i", nm, mid, b, a).unwrap(); nm
    }
    let t = tr(s, name, 0, bl.len());
    writeln!(s, "def {} : Nat → Nat := {}", name, t).unwrap();
}

// packed context of level index `lvl`: tables CC (compact cov), CS (spread cov), PC, TC; row and cbJ read them; cntF := cfRef
fn lean_ctx_packed(lvl: usize, lv: &Level) -> String {
    let n = lv.n; let wc = n + 1; let ws = 16 * (n + 1);
    let gc = (32768 / wc).max(1).min(128); let gs = (32768 / ws).max(1).min(64); let (gc, gs) = match std::env::var("GPACK").ok().and_then(|v| v.parse::<usize>().ok()) { Some(g) => (g, g), None => (gc, gs) };
    let (ncw, nsw) = ((wc + 63) / 64 + 1, (ws + 63) / 64 + 1);
    let mut cc = vec![vec![0u64; ncw]; n + 1]; let mut cs = vec![vec![0u64; nsw]; n + 1];
    let mut pcv = vec![vec![0u64; nsw]; n + 1]; let mut tcv = vec![vec![0u64; nsw]; n + 1];
    for x in 1..=n {
        cc[x] = words_bits(&bits(&lv.cov[x]), 1, ncw); cs[x] = words_bits(&bits(&lv.cov[x]), 16, nsw);
        if lvl >= 1 { pcv[x] = words_bits(&bits(&lv.pcls[x]), 16, nsw); }
        if lvl >= 2 { tcv[x] = words_bits(&bits(&lv.tcls[x]), 16, nsw); }
    }
    let mut s = String::new();
    emit_table(&mut s, &format!("L{}CC", lvl), &cc, wc, gc);
    emit_table(&mut s, &format!("L{}CS", lvl), &cs, ws, gs);
    if lvl >= 1 { emit_table(&mut s, &format!("L{}PC", lvl), &pcv, ws, gs); }
    if lvl >= 2 { emit_table(&mut s, &format!("L{}TC", lvl), &tcv, ws, gs); }
    writeln!(s, "def L{}cbP (j : Nat) : Nat := pk L{}CS {} {} j", lvl, lvl, ws, gs).unwrap();
    let pcx = if lvl >= 1 { format!("pk L{}PC {} {} (Nat.div (Nat.log2 b) 16)", lvl, ws, gs) } else { "0".into() };
    let tcx = if lvl >= 2 { format!("pk L{}TC {} {} (Nat.div (Nat.log2 b) 16)", lvl, ws, gs) } else { "0".into() };
    writeln!(s, "def L{}rowP (b : Nat) : Nat × Nat × Nat × Nat :=\n  (Nat.div (Nat.log2 b) 16, pk L{}CC {} {} (Nat.div (Nat.log2 b) 16), {}, {})", lvl, lvl, wc, gc, pcx, tcx).unwrap();
    let cnt = if std::env::var("CFMODE").map(|v| v == "unrolled").unwrap_or(false) {
        // TIMING VARIANT ONLY (not a valid table statement): old unrolled counter tree over the packed cbP
        fn cft(s: &mut String, lvl: usize, lo: usize, hi: usize) -> String {
            let name = format!("cf{}_{}_{}", lvl, lo, hi);
            if hi - lo == 1 { writeln!(s, "def {} (u acc : Nat) : Nat := bif Nat.beq (Nat.land u {}) (nat_lit 0) then acc else Nat.add acc (L{}cbP {})", name, pow2_lit(lo), lvl, lo).unwrap(); return name; }
            let mid = (lo + hi) / 2; let a = cft(s, lvl, lo, mid); let b = cft(s, lvl, mid, hi);
            writeln!(s, "def {} (u acc : Nat) : Nat := bif Nat.beq (Nat.land u {}) (nat_lit 0) then acc else {} u ({} u acc)", name, maskrange_lit(lo, hi), a, b).unwrap(); name
        }
        cft(&mut s, lvl, 1, n + 1)
    } else { format!("cfRef L{}cbP 13 1 ((nat_lit {}) + 1)", lvl, n) };
    writeln!(s, "def X{} : Ctx := {{ lvl := nat_lit {}, W := nat_lit {}, full := {}, adm := {}, m3 := {}, ones := {}, lowp := {}, lowT := {}, row := L{}rowP, cbJ := L{}cbP, cntF := {} }}",
        lvl, lvl, n, compact_lit(&lv.full), spread_lit(&lv.adm), spread_lit(&lv.m3), spread_lit_with0(&Z, n), spread_lit(&lv.lowp), spread_lit(&lv.lowt), lvl, lvl, cnt).unwrap();
    s
}

fn ghdr(p: usize, imports: &str, ns: &str, opens: &str) -> String {
    format!("/- GENERATED by gen_prime (per-prime tables; not part of any aggregator) -/\n{}\n\nnamespace LRSpectrumFull.NineSound.G{}.{}\nopen {}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\nnoncomputable section\n\n", imports, p, ns, opens)
}

// table-check modules of level lvl: scalar module, row chunk modules, cb chunk modules, assembly. Returns the list of file names written.
fn emit_tab_level(p: usize, lvl: usize, n: usize, rc: usize, cc: usize, permod: usize, outdir: &str) -> Vec<String> {
    let dmod = if lvl == 2 { "D2" } else { "D01" };
    let base = format!("import LRSpectrumFull.NineSound.TabChunk\nimport LRSpectrumFull.NineSound.G{}.{}", p, dmod);
    let opens = format!("LRSpectrumFull.NineProbe LRSpectrumFull.NineSound LRSpectrumFull.NineSound.G{}.{}", p, dmod);
    let mut files = vec![]; let mut imports = String::new();
    // scalar module
    let nm = format!("T{}S", lvl);
    let mut m = ghdr(p, &base, &nm, &opens);
    writeln!(m, "theorem sc : ScalFin9 X{} {} {} := by decide +kernel\n\nend\nend LRSpectrumFull.NineSound.G{}.{}", lvl, lvl, p, p, nm).unwrap();
    fs::write(format!("{}/{}.lean", outdir, nm), &m).unwrap(); files.push(nm.clone());
    writeln!(imports, "import LRSpectrumFull.NineSound.G{}.{}", p, nm).unwrap();
    // chunks
    let mut proof_rows = String::from("  have h0 := rows_base X{L} {L} {P}\n"); let mut proof_cb = String::from("  have h0 := cb_base X{L} {L} {P}\n");
    let mut chain_names: Vec<(String, usize, usize, bool)> = vec![];
    for (kind, size) in [("R", rc), ("C", cc)] {
        let mut lo = 1; let mut k = 0; let mut inmod = 0; let mut nmcur = String::new(); let mut mcur = String::new();
        while lo <= n {
            let hi = (lo + size).min(n + 1);
            if inmod == 0 {
                nmcur = format!("T{}{}{}", lvl, kind, k); mcur = ghdr(p, &base, &nmcur, &opens); k += 1;
            }
            let (ty, nme) = if kind == "R" { ("RowChunk", format!("rc_{}_{}", lo, hi)) } else { ("CbChunk", format!("cc_{}_{}", lo, hi)) };
            writeln!(mcur, "theorem {} : {} X{} {} {} {} {} := by decide +kernel", nme, ty, lvl, lvl, p, lo, hi).unwrap();
            chain_names.push((format!("LRSpectrumFull.NineSound.G{}.{}.{}", p, nmcur, nme), lo, hi, kind == "R"));
            inmod += 1; lo = hi;
            if inmod == permod || lo > n {
                writeln!(mcur, "\nend\nend LRSpectrumFull.NineSound.G{}.{}", p, nmcur).unwrap();
                fs::write(format!("{}/{}.lean", outdir, nmcur), &mcur).unwrap(); files.push(nmcur.clone());
                writeln!(imports, "import LRSpectrumFull.NineSound.G{}.{}", p, nmcur).unwrap();
                inmod = 0;
            }
        }
    }
    let (mut ri, mut ci) = (0, 0);
    for (full, _lo, _hi, isrow) in &chain_names {
        if *isrow { writeln!(proof_rows, "  have h{} := rows_step h{} {}", ri + 1, ri, full).unwrap(); ri += 1; }
        else { writeln!(proof_cb, "  have h{} := cb_step h{} {}", ci + 1, ci, full).unwrap(); ci += 1; }
    }
    let proof_rows = proof_rows.replace("{L}", &lvl.to_string()).replace("{P}", &p.to_string());
    let proof_cb = proof_cb.replace("{L}", &lvl.to_string()).replace("{P}", &p.to_string());
    let nm = format!("T{}A", lvl); let base = format!("{}\nimport LRSpectrumFull.NineSound.TabChunk2", base);
    let mut m = format!("/- GENERATED by gen_prime: assembly of the table statement of level {} at p = {} -/\n{}{}\n\nnamespace LRSpectrumFull.NineSound.G{}.{}\nopen LRSpectrumFull.NineProbe LRSpectrumFull.NineSound LRSpectrumFull.NineSound.G{}.{}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n", lvl, p, base, "\n", p, nm, p, dmod);
    // imports must precede namespace: rebuild header with chunk imports
    m = format!("/- GENERATED by gen_prime: assembly of the table statement of level {} at p = {} -/\n{}\n{}\nnamespace LRSpectrumFull.NineSound.G{}.{}\nopen LRSpectrumFull.NineProbe LRSpectrumFull.NineSound LRSpectrumFull.NineSound.G{}.{}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n", lvl, p, base, imports, p, nm, p, dmod);
    writeln!(m, "theorem rows : RowsUpTo X{} {} {} (X{}.W + 1) := by\n{}  exact h{}\n", lvl, lvl, p, lvl, proof_rows, ri).unwrap();
    writeln!(m, "theorem cbs : CbUpTo X{} {} {} (X{}.W + 1) := by\n{}  exact h{}\n", lvl, lvl, p, lvl, proof_cb, ci).unwrap();
    writeln!(m, "theorem tableOK9g_X{} : TableOK9g X{} {} {} :=\n  tableOK9g_of_partsF _ _ _ LRSpectrumFull.NineSound.G{}.T{}S.sc rows cbs (by decide) (fun _ _ => rfl)\n\nend LRSpectrumFull.NineSound.G{}.{}", lvl, lvl, lvl, p, p, lvl, p, nm).unwrap();
    fs::write(format!("{}/{}.lean", outdir, nm), &m).unwrap(); files.push(nm);
    files
}
fn lean_st(name: &str, s: &S) -> String {
    format!("def {} : St := {{ unc := {}, cu := (nat_lit 0), nu := (nat_lit 0), av := {}, fr := (nat_lit {}), r := (nat_lit {}), c3 := (nat_lit {}), ch := {}, im := {}, it := {}, mp := {}, mq := {}, mf := {} }}",
        name, compact_lit(&s.unc), spread_lit(&s.av), s.fr, s.r, s.c3, spread_lit(&s.ch), spread_lit(&s.im), spread_lit(&s.it), spread_lit(&s.mp), spread_lit(&s.mq), spread_lit(&s.mf))
}

struct Tree { desc: (B, B, usize), stream: Vec<u16>, infeasible: bool, nodes: u64 }
struct Task { h: S, stream: Vec<u16>, nodes: usize }

struct Eng<'a> {
    lvs: &'a [Level], p: usize, cur: Vec<u16>, nodes: Vec<u64>, leaves: Vec<u64>, pnc: Vec<u64>, pbd: Vec<u64>, prt: Vec<u64>, surv: u64,
    trees: Vec<Vec<Tree>>, idx0: usize, sizes0: Vec<usize>, real: bool, lim: usize, tasks: Vec<Task>, top_stream: Vec<u16>,
    kinds: [u64; 4], // branch, bound, nocov, leaf(5)
}

impl<'a> Eng<'a> {
    fn root_state(&self, li: usize, d: &(B, B, usize)) -> S {
        let lv = &self.lvs[li];
        let (icm, ict, fr) = (d.0, d.1, d.2);
        let mut mp = Z; for c in bits(&icm) { mp = or(&mp, &lv.pcls[c]); }
        let mut mq = Z; let mut mf = Z; let mut c3 = 0;
        for c in bits(&ict) { if c % 3 == 0 { mf = or(&mf, &lv.tcls[c]); c3 += 1; } else { mq = or(&mq, &lv.tcls[c]); } }
        assert_eq!(pc(&icm) + pc(&ict) + fr, K);
        S { unc: lv.full, av: lv.adm, fr, r: K, c3, ch: Z, im: icm, it: ict, mp, mq, mf }
    }

    fn make_tree(&mut self, li: usize, d: (B, B, usize)) -> usize { // returns tree index at level li (>=1)
        let idx = self.trees[li].len();
        self.trees[li].push(Tree { desc: d, stream: vec![], infeasible: false, nodes: 0 });
        let s = self.root_state(li, &d);
        let n0 = self.nodes[li];
        if s.c3 > K - 2 { self.nodes[li] += 1; self.prt[li] += 1; self.trees[li][idx].infeasible = true; self.trees[li][idx].nodes = 1; return idx; }
        let saved = std::mem::take(&mut self.cur);
        self.node(li, &s, true);
        let st = std::mem::replace(&mut self.cur, saved);
        self.trees[li][idx].stream = st; self.trees[li][idx].nodes = self.nodes[li] - n0;
        idx
    }

    fn node(&mut self, li: usize, s: &S, in_task: bool) {
        if li == 0 {
            let my = self.idx0; self.idx0 += 1;
            if self.real && !in_task && self.sizes0[my] <= self.lim {
                let tid = self.tasks.len(); self.cur.push(7); self.cur.push(tid as u16);
                self.tasks.push(Task { h: s.clone(), stream: vec![], nodes: 0 });
                let saved = std::mem::take(&mut self.cur);
                let n0 = self.nodes[0];
                self.body(li, s, true);
                let st = std::mem::replace(&mut self.cur, saved);
                self.tasks[tid].stream = st; self.tasks[tid].nodes = (self.nodes[0] - n0) as usize;
            } else { self.body(li, s, in_task); }
            if !self.real { self.sizes0[my] = self.idx0 - my; }
        } else { self.body(li, s, in_task); }
    }

    fn body(&mut self, li: usize, s: &S, in_task: bool) {
        let lvs = self.lvs; let lv = &lvs[li];
        self.nodes[li] += 1;
        let nu = pc(&s.unc);
        if nu == 0 {
            self.leaves[li] += 1;
            if li + 1 < lvs.len() {
                let d = if li == 0 { (s.ch, Z, s.fr) } else { (s.im, s.ch, s.fr) };
                self.cur.push(5);
                let pos = self.cur.len(); self.cur.push(0);
                let i = self.make_tree(li + 1, d);
                self.cur[pos] = i as u16; self.kinds[3] += 1;
            } else { self.surv += 1; self.cur.push(6); }
            return;
        }
        // allowed set (the Lean `allowed`)
        let f = if s.c3 > K - 3 { lv.m3 } else { Z };
        let a0 = or(&if s.fr == 0 { Z } else { s.av }, &and(&or(&s.mp, &s.mq), &s.av));
        let a = or(&andn(&a0, &f), &and(&s.mf, &s.av));
        // branching time: fewest allowed coverers (first minimum, stop at 0)
        let mut bj = 0; let mut bm = usize::MAX;
        for t in bits(&s.unc) { let c = pc(&and(&lv.cov[t], &a)); if c < bm { bm = c; bj = t; if c == 0 { break; } } }
        if bm == 0 { self.pnc[li] += 1; self.kinds[2] += 1; self.cur.push(2); self.cur.push(bj as u16); return; }
        // bound with hint
        let xs = bits(&a); let cl: Vec<(usize, usize)> = xs.iter().map(|&x| (x, pc(&and(&lv.cov[x], &s.unc)))).collect();
        let mut sorted: Vec<usize> = cl.iter().map(|c| c.1).collect(); sorted.sort_unstable_by(|a, b| b.cmp(a));
        let r = s.r; assert!(r >= 1);
        let (t, tset, tot) = if cl.len() >= r {
            let t = sorted[r - 1]; let ts: Vec<(usize, usize)> = cl.iter().cloned().filter(|c| c.1 > t).collect();
            let sm: usize = ts.iter().map(|c| c.1).sum(); (t, ts.clone(), sm + (r - ts.len()) * t)
        } else { let sm: usize = cl.iter().map(|c| c.1).sum(); (0, cl.clone(), sm) };
        if tot < nu {
            self.pbd[li] += 1; self.kinds[1] += 1;
            self.cur.push(3); self.cur.push(t as u16); self.cur.push(tset.len() as u16); for c in &tset { self.cur.push(c.0 as u16); }
            return;
        }
        // branch
        self.kinds[0] += 1; self.cur.push(0); self.cur.push(bj as u16);
        let cands = bits(&and(&lv.cov[bj], &a));
        let mut av2 = s.av;
        for &x in &cands {
            av2[(x - 1) >> 6] &= !(1u64 << ((x - 1) & 63));
            let inp = tb(&s.mp, x); let inq = tb(&s.mq, x); let inf = tb(&s.mf, x); let role = inp || inq || inf;
            let mut c = s.clone();
            c.unc = andn(&s.unc, &lv.cov[x]); c.av = av2;
            c.fr = if role { s.fr } else { s.fr - 1 }; c.r = s.r - 1;
            c.c3 = s.c3 + (if x % 3 == 0 && li > 0 { 1 } else { 0 }) - (if inf { 1 } else { 0 });
            sb(&mut c.ch, x);
            if inp { c.im = andn(&s.im, &and(&lv.pcls[x], &lv.lowp)); c.mp = andn(&s.mp, &lv.pcls[x]); }
            if inq || inf { c.it = andn(&s.it, &and(&lv.tcls[x], &lv.lowt)); }
            if inq { c.mq = andn(&s.mq, &lv.tcls[x]); }
            if inf { c.mf = andn(&s.mf, &lv.tcls[x]); }
            self.node(li, &c, in_task);
        }
    }
}

fn run(p: usize, lim: usize, real: bool, sizes0: Vec<usize>, nlev: usize) -> Eng<'static> {
    let mut lvs = vec![]; let mut l = 1; let mults = [1usize, 3, 3];
    for i in 0..nlev { l *= mults[i]; lvs.push(build_level(p, l)); }
    let lvs: &'static [Level] = Box::leak(lvs.into_boxed_slice());
    let mut e = Eng { lvs, p, cur: vec![], nodes: vec![0; nlev], leaves: vec![0; nlev], pnc: vec![0; nlev], pbd: vec![0; nlev], prt: vec![0; nlev], surv: 0,
        trees: (0..nlev).map(|_| vec![]).collect(), idx0: 0, sizes0, real, lim, tasks: vec![], top_stream: vec![], kinds: [0; 4] };
    let lv = &lvs[0];
    let unc = andn(&lv.full, &lv.cov[1]); let mut av = lv.adm; av[0] &= !1u64; let mut ch = Z; sb(&mut ch, 1);
    let root = S { unc, av, fr: 7, r: 7, c3: 0, ch, im: Z, it: Z, mp: Z, mq: Z, mf: Z };
    e.node(0, &root, false);
    e.top_stream = std::mem::take(&mut e.cur);
    let _ = e.p;
    e
}

fn write_chunks(out: &mut String, name: &str, f: &[u16]) {
    let ch = nat16(f, 256);
    for (i, c) in ch.iter().enumerate() { writeln!(out, "def {}_R{} : Nat := {}", name, i, c).unwrap(); }
    fn tr(out: &mut String, name: &str, lo: usize, hi: usize) -> String {
        let nm = format!("{}_T{}_{}", name, lo, hi);
        if hi - lo == 1 { writeln!(out, "def {} (_ : Nat) : Nat := {}_R{}", nm, name, lo).unwrap(); return nm; }
        let mid = (lo + hi) / 2; let a = tr(out, name, lo, mid); let b = tr(out, name, mid, hi);
        writeln!(out, "def {} (i : Nat) : Nat := bif Nat.ble (nat_lit {}) i then {} i else {} i", nm, mid, b, a).unwrap(); nm
    }
    let t = tr(out, name, 0, ch.len());
    writeln!(out, "def {} : Nat → Nat := {}", name, t).unwrap();
}

// ---------- per-prime driver ----------
// usage: gen_prime P OUTDIR LIM NODES_PER_CHUNK PERMOD RC0 CC0 RC1 CC1 RC2 CC2 [MODE]    MODE = stats | emit
// Emits, for one prime, the Lean modules: D01 D2 Desc (contexts, descriptor lists), table-check modules T<l>S/R/C/A,
// task data TD<c>, TG (task list), TK<c> (chunk checks), Top (level-0 tree), LD1_<c> LG1 LK1_<c>, LD2_<c> LG2 LK2_<c>,
// Ctl9 (planted corruptions), PD (assembly of PrimeData p), and order.txt (build order).
fn plan(nodes: &[usize], target: usize) -> Vec<(usize, usize, usize)> {
    let mut out = vec![]; let mut i = 0;
    while i < nodes.len() {
        let mut j = i; let mut acc = 0;
        while j < nodes.len() && (j == i || acc + nodes[j] <= target) { acc += nodes[j]; j += 1; }
        out.push((i, j - i, acc)); i = j;
    }
    out
}

// chunked balanced table: `name : Nat -> ty` (unclamped; callers use `clampT name nameN`).  Leaves are lists of B entries read
// with `List.getD` (at most B steps); the tree above them has depth log2(#leaves), one definition per node.
fn emit_ctab(s: &mut String, name: &str, ty: &str, dflt: &str, entries: &[String]) {
    const B: usize = 32;
    assert!(!entries.is_empty());
    let nc = (entries.len() + B - 1) / B;
    for j in 0..nc {
        let hi = ((j + 1) * B).min(entries.len());
        writeln!(s, "def {}_C{} : List ({}) := [{}]", name, j, ty, entries[j * B..hi].join(",\n  ")).unwrap();
    }
    fn tr(s: &mut String, name: &str, ty: &str, dflt: &str, lo: usize, hi: usize) -> String {
        let nm = format!("{}_N{}_{}", name, lo, hi);
        if hi - lo == 1 { writeln!(s, "def {} (i : Nat) : {} := {}_C{}.getD (Nat.sub i (nat_lit {})) {}", nm, ty, name, lo, lo * B, dflt).unwrap(); return nm; }
        let mid = (lo + hi) / 2; let a = tr(s, name, ty, dflt, lo, mid); let b = tr(s, name, ty, dflt, mid, hi);
        writeln!(s, "def {} (i : Nat) : {} := bif Nat.ble (nat_lit {}) i then {} i else {} i", nm, ty, mid * B, b, a).unwrap(); nm
    }
    let t = tr(s, name, ty, dflt, 0, nc);
    writeln!(s, "def {} : Nat → {} := {}", name, ty, t).unwrap();
}
// table of tree streams from the per-chunk lists `Str<lv>L<c>` (starts[c] = first tree of chunk c): leaf c reads its local list (<= chunk size steps)
fn emit_stream_tab(s: &mut String, name: &str, lists: &[String], starts: &[usize]) {
    fn tr(s: &mut String, name: &str, lists: &[String], starts: &[usize], lo: usize, hi: usize) -> String {
        let nm = format!("{}_N{}_{}", name, lo, hi);
        if hi - lo == 1 { writeln!(s, "def {} (k : Nat) : List Nat := gtab {} (Nat.sub k (nat_lit {}))", nm, lists[lo], starts[lo]).unwrap(); return nm; }
        let mid = (lo + hi) / 2; let a = tr(s, name, lists, starts, lo, mid); let b = tr(s, name, lists, starts, mid, hi);
        writeln!(s, "def {} (k : Nat) : List Nat := bif Nat.ble (nat_lit {}) k then {} k else {} k", nm, starts[mid], b, a).unwrap(); nm
    }
    let t = tr(s, name, lists, starts, 0, lists.len());
    writeln!(s, "def {} : Nat → List Nat := {}", name, t).unwrap();
}

fn st_expr(s: &S) -> String {
    format!("{{ unc := {}, cu := (nat_lit 0), nu := (nat_lit 0), av := {}, fr := (nat_lit {}), r := (nat_lit {}), c3 := (nat_lit {}), ch := {}, im := {}, it := {}, mp := {}, mq := {}, mf := {} }}",
        compact_lit(&s.unc), spread_lit(&s.av), s.fr, s.r, s.c3, spread_lit(&s.ch), spread_lit(&s.im), spread_lit(&s.it), spread_lit(&s.mp), spread_lit(&s.mq), spread_lit(&s.mf))
}
fn blobs(f: &[u16]) -> String { format!("[{}]", nat16(f, 256).join(", ")) }
fn desc_expr(d: &(B, B, usize)) -> String { format!("({}, {}, (nat_lit {}))", spread_lit(&d.0), spread_lit(&d.1), d.2) }
fn foldapp(names: &[String]) -> String {
    let mut s = names[names.len() - 1].clone();
    for n in names[..names.len() - 1].iter().rev() { s = format!("{} ++ ({})", n, s); }
    s
}
// first bound-leaf record (tag 3) of a stream whose threshold t is odd and >= 1: returns the field index of t
fn find_corrupt(f: &[u16]) -> Option<usize> {
    let mut pos = 0;
    while pos < f.len() {
        match f[pos] {
            0 | 2 | 5 | 7 => pos += 2,
            3 => { let t = f[pos + 1]; let n = f[pos + 2] as usize; if t % 2 == 1 { return Some(pos + 1); } pos += 3 + n; }
            _ => return None,
        }
    }
    None
}

fn st_same(a: &S, b: &S) -> bool {
    a.unc == b.unc && a.av == b.av && a.fr == b.fr && a.r == b.r && a.c3 == b.c3 && a.ch == b.ch && a.im == b.im
        && a.it == b.it && a.mp == b.mp && a.mq == b.mq && a.mf == b.mf
}
// first delegation record `7 i` of the top stream with i xor 1 a different task state: returns the field index of i (flip bit 0)
fn find_corrupt_deleg(f: &[u16], tasks: &[Task]) -> Option<usize> {
    let mut pos = 0;
    while pos < f.len() {
        match f[pos] {
            0 | 2 | 5 => pos += 2,
            7 => { let i = f[pos + 1] as usize; let j = i ^ 1;
                   if j < tasks.len() && !st_same(&tasks[i].h, &tasks[j].h) { return Some(pos + 1); } pos += 2; }
            3 => { let n = f[pos + 2] as usize; pos += 3 + n; }
            _ => return None,
        }
    }
    None
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p: usize = a[1].parse().unwrap(); let outdir = a[2].clone(); let lim: usize = a[3].parse().unwrap();
    let target: usize = a[4].parse().unwrap(); let permod: usize = a[5].parse().unwrap();
    let rcs = [a[6].parse::<usize>().unwrap(), a[8].parse::<usize>().unwrap(), a[10].parse::<usize>().unwrap()];
    let ccs = [a[7].parse::<usize>().unwrap(), a[9].parse::<usize>().unwrap(), a[11].parse::<usize>().unwrap()];
    let mode = if a.len() > 12 { a[12].clone() } else { "stats".into() };
    let nlev = 3;
    let dry = run(p, lim, false, vec![0; 6_000_000], nlev);
    let total0 = dry.idx0;
    let sizes0: Vec<usize> = dry.sizes0[..total0].to_vec();
    println!("DRY p {} level-0 nodes {} | per level nodes {:?} leaves {:?} survivors {} | trees L1 {} L2 {}",
        p, dry.nodes[0], dry.nodes, dry.leaves, dry.surv, dry.trees[1].len(), dry.trees[2].len());
    let e = run(p, lim, true, sizes0, nlev);
    let tot: u64 = e.nodes.iter().sum();
    let tn: Vec<usize> = e.tasks.iter().map(|t| t.nodes).collect();
    println!("REAL nodes total {} | tasks {} (max {}, min {}) | top stream fields {} | W = {:?}", tot, e.tasks.len(), tn.iter().max().unwrap_or(&0), tn.iter().min().unwrap_or(&0),
        e.top_stream.len(), e.lvs.iter().map(|l| l.n).collect::<Vec<_>>());
    let tplan = plan(&tn, target);
    let n1n: Vec<usize> = e.trees[1].iter().map(|t| t.nodes as usize).collect();
    let n2n: Vec<usize> = e.trees[2].iter().map(|t| t.nodes as usize).collect();
    let p1 = plan(&n1n, target); let p2 = plan(&n2n, target);
    println!("PLAN task chunks {} (nodes per chunk max {}) | L1 trees {} chunks {} | L2 trees {} chunks {}", tplan.len(), tplan.iter().map(|c| c.2).max().unwrap_or(0),
        e.trees[1].len(), p1.len(), e.trees[2].len(), p2.len());
    // Model of the earlier list-lookup generator (list lookups gtab D1L i, gtab Str1L k cost O(index) kernel steps, ~9.5 KB each, cached for the
    // whole module; calibrated on a micro experiment at p = 61: 100 lookups at index 0/3000/6300 = 715/3600/6649 MB).  Not a claim about this
    // generator, which has no list lookups.
    {
        let mut tk_steps = 0usize; let mut tk_leaves = 0usize; let mut perchunk: Vec<usize> = vec![];
        for &(st, n, _) in &tplan {
            let (mut s, mut lc) = (0usize, 0usize);
            for t in &e.tasks[st..st + n] {
                let f = &t.stream; let mut pos = 0;
                while pos < f.len() { match f[pos] { 0 | 2 | 7 => pos += 2, 5 => { s += f[pos + 1] as usize; lc += 1; pos += 2; } 3 => { pos += 3 + f[pos + 2] as usize; } _ => break } }
            }
            perchunk.push(700 + s * 94 / 10000); if s > tk_steps { tk_steps = s; tk_leaves = lc; }
        }
        let mut lk_steps = 0usize;
        for &(st, n, _) in &p1 {
            let s: usize = (st..st + n).map(|k| k + 1).sum();
            if s > lk_steps { lk_steps = s; }
        }
        // The Top module of gen_prime12 looks up every delegated state with `gtab HSL i` (list, O(i) steps, ~9.4 KB each, cached per
        // (suffix, remaining index), so n lookups cost n^2/2 steps).  Measured on p = 163 (S13A diag, lookups only): 400/800/1200 lookups = 1533/3956/7641 MB.
        println!("PRED_OLD_TOP n_tasks {} -> {} MB (list form, gen_prime12 only; gen_prime13 uses a balanced table, no n^2 term)", e.tasks.len(), 1200 + e.tasks.len() * e.tasks.len() * 46 / 10000);
        println!("PRED_OLD_TK_PER_CHUNK_MB {:?}", perchunk);
        println!("PRED_OLD tk_steps_max {} (leaves {}) -> {} MB | lk1_steps_max {} -> {} MB", tk_steps, tk_leaves, 700 + tk_steps * 94 / 10000, lk_steps, 700 + lk_steps * 94 / 10000);
    }
    if mode == "stats" { return; }
    assert!(!e.tasks.is_empty() && !e.trees[1].is_empty() && !e.trees[2].is_empty());
    fs::create_dir_all(&outdir).unwrap();
    let mut order: Vec<String> = vec![];
    let wr = |nm: &str, s: &str| { fs::write(format!("{}/{}.lean", outdir, nm), s).unwrap(); };
    let g = |nm: &str| format!("LRSpectrumFull.NineSound.G{}.{}", p, nm);
    let imp = "import LRSpectrumFull.NineProbe.Check\nimport LRSpectrumFull.NineProbe.Tabs";
    let close = |nm: &str| format!("\nend\nend {}\n", g(nm));
    // contexts
    let mut b = ghdr(p, imp, "D01", "LRSpectrumFull.NineProbe");
    b.push_str(&lean_ctx_old("D", 0, p, &e.lvs[0])); b.push_str(&lean_ctx_old("D", 1, p, &e.lvs[1])); b.push_str(&close("D01"));
    wr("D01", &b); order.push("D01".into());
    let mut b = ghdr(p, imp, "D2", "LRSpectrumFull.NineProbe");
    b.push_str(&lean_ctx_old("D", 2, p, &e.lvs[2])); b.push_str(&close("D2"));
    wr("D2", &b); order.push("D2".into());
    // descriptor lists
    // gen_prime12: the level-1/2 descriptor tables are logarithmic-depth functions D1T, D2T with sizes D1N, D2N
    // (NineProbe/DrvF.lean: clampT), not lists; a list lookup costs O(index) kernel steps.
    let mut b = ghdr(p, "import LRSpectrumFull.NineProbe.Check\nimport LRSpectrumFull.NineProbe.DrvF", "Desc", "LRSpectrumFull.NineProbe");
    for (nm, lv) in [("D1", 1usize), ("D2", 2usize)] {
        let ents: Vec<String> = e.trees[lv].iter().map(|t| desc_expr(&t.desc)).collect();
        emit_ctab(&mut b, &format!("{}T", nm), "Nat × Nat × Nat", "((nat_lit 0), (nat_lit 0), (nat_lit 0))", &ents);
        writeln!(b, "def {}N : Nat := nat_lit {}", nm, ents.len()).unwrap();
    }
    b.push_str(&close("Desc")); wr("Desc", &b); order.push("Desc".into());
    // tables
    let mut tabmods: Vec<String> = vec![];
    for lvl in 0..3 {
        let files = emit_tab_level(p, lvl, e.lvs[lvl].n, rcs[lvl], ccs[lvl], permod, &outdir);
        for f in &files { order.push(f.clone()); }
        tabmods.push(format!("T{}A", lvl));
    }
    // task data and chunk checks
    let drv = "import LRSpectrumFull.NineProbe.Drv";
    let mut tdn = vec![];
    for (c, &(st, n, _)) in tplan.iter().enumerate() {
        let nm = format!("TD{}", c);
        let mut m = ghdr(p, drv, &nm, "LRSpectrumFull.NineProbe");
        let items: Vec<String> = (st..st + n).map(|i| format!("(noH 0, {})", blobs(&e.tasks[i].stream))).collect();
        writeln!(m, "def TaskL{} : List (St × List Nat) := [{}]", c, items.join(",\n  ")).unwrap();
        m.push_str(&close(&nm)); wr(&nm, &m); order.push(nm.clone()); tdn.push(nm);
    }
    {
        let mut m = ghdr(p, drv, "TS", "LRSpectrumFull.NineProbe");
        let items: Vec<String> = e.tasks.iter().map(|t| st_expr(&t.h)).collect();
        emit_ctab(&mut m, "HST", "St", "(noH 0)", &items);
        writeln!(m, "def HSN : Nat := nat_lit {}", items.len()).unwrap();
        m.push_str(&close("TS")); wr("TS", &m); order.push("TS".into());
    }
    let mut m = ghdr(p, &tdn.iter().map(|n| format!("import {}", g(n))).collect::<Vec<_>>().join("\n").replace("\n", "\n"), "TG", "LRSpectrumFull.NineProbe");
    m = m.replacen("import", &format!("{}\nimport", drv), 1);
    let opens: Vec<String> = tdn.iter().map(|n| g(n)).collect();
    m = m.replacen("noncomputable section", &format!("open {}\nnoncomputable section", opens.join(" ")), 1);
    writeln!(m, "def TaskCH : List (List (St × List Nat)) := [{}]\ndef TaskSt : List Nat := [{}]\ndef TaskN : Nat := {}", (0..tplan.len()).map(|c| format!("TaskL{}", c)).collect::<Vec<_>>().join(", "), tplan.iter().map(|c| c.0.to_string()).collect::<Vec<_>>().join(", "), tplan.iter().map(|c| c.1).sum::<usize>()).unwrap();
    m.push_str(&close("TG")); wr("TG", &m); order.push("TG".into());
    let mut tkn = vec![];
    for (c, &(st, n, _)) in tplan.iter().enumerate() {
        let nm = format!("TK{}", c);
        let imps = format!("import {}\nimport {}\nimport {}\nimport {}", g("D01"), g("Desc"), g("TG"), g("TS"));
        let mut m = ghdr(p, &imps, &nm, &format!("LRSpectrumFull.NineProbe {} {} {} {}", g("D01"), g("Desc"), g("TG"), g("TS")));
        writeln!(m, "theorem chk : allTasks X0 TaskCH TaskSt TaskN (clampT HST HSN) (clampT D1T D1N) {} {} = true := by decide +kernel", st, n).unwrap();
        m.push_str(&close(&nm)); wr(&nm, &m); order.push(nm.clone()); tkn.push(nm);
    }
    // top tree
    {
        let imps = format!("import {}\nimport {}\nimport {}", g("D01"), g("Desc"), g("TS"));
        let mut m = ghdr(p, &imps, "Top", &format!("LRSpectrumFull.NineProbe {} {} {}", g("D01"), g("Desc"), g("TS")));
        writeln!(m, "def C0L : List Nat := {}\ndef C0 : Nat → Nat := fun i => C0L.getD i 0", blobs(&e.top_stream)).unwrap();
        writeln!(m, "theorem top_ok : checkTree0 X0 C0 (clampT HST HSN) (clampT D1T D1N) = true := by decide +kernel").unwrap();
        m.push_str(&close("Top")); wr("Top", &m); order.push("Top".into());
    }
    // level 1 and level 2 trees
    let mut lkn: Vec<Vec<String>> = vec![vec![], vec![]];
    for (li, lv) in [1usize, 2usize].iter().enumerate() {
        let pl = if li == 0 { &p1 } else { &p2 };
        let mut ldn = vec![];
        for (c, &(st, n, _)) in pl.iter().enumerate() {
            let nm = format!("LD{}_{}", lv, c);
            let mut m = ghdr(p, drv, &nm, "LRSpectrumFull.NineProbe");
            let items: Vec<String> = (st..st + n).map(|i| blobs(&e.trees[*lv][i].stream)).collect();
            writeln!(m, "def Str{}L{} : List (List Nat) := [{}]", lv, c, items.join(",\n  ")).unwrap();
            m.push_str(&close(&nm)); wr(&nm, &m); order.push(nm.clone()); ldn.push(nm);
        }
        let gname = format!("LG{}", lv);
        let mut m = ghdr(p, &format!("{}\n{}", drv, ldn.iter().map(|n| format!("import {}", g(n))).collect::<Vec<_>>().join("\n")), &gname, "LRSpectrumFull.NineProbe");
        let opens: Vec<String> = ldn.iter().map(|n| g(n)).collect();
        m = m.replacen("noncomputable section", &format!("open {}\nnoncomputable section", opens.join(" ")), 1);
        let lists: Vec<String> = (0..pl.len()).map(|c| format!("Str{}L{}", lv, c)).collect();
        let starts: Vec<usize> = pl.iter().map(|c| c.0).collect();
        emit_stream_tab(&mut m, &format!("S{}T", lv), &lists, &starts);
        m.push_str(&close(&gname)); wr(&gname, &m); order.push(gname.clone());
        for (c, &(st, n, _)) in pl.iter().enumerate() {
            let nm = format!("LK{}_{}", lv, c);
            let ctxmod = if *lv == 1 { "D01" } else { "D2" };
            let imps = format!("import {}\nimport {}\nimport {}", g(ctxmod), g("Desc"), g(&gname));
            let mut m = ghdr(p, &imps, &nm, &format!("LRSpectrumFull.NineProbe {} {} {}", g(ctxmod), g("Desc"), g(&gname)));
            if *lv == 1 { writeln!(m, "theorem chk : allRootsF X1 (ctT S1T D1N) (clampT D2T D2N) (clampT D1T D1N) {} {} = true := by decide +kernel", st, n).unwrap(); }
            else { writeln!(m, "theorem chk : allRootsF X2 (ctT S2T D2N) (fun _ => (0, 0, 0)) (clampT D2T D2N) {} {} = true := by decide +kernel", st, n).unwrap(); }
            m.push_str(&close(&nm)); wr(&nm, &m); order.push(nm.clone()); lkn[li].push(nm);
        }
    }
    // controls: planted corruptions
    {
        let imps = format!("import {}\nimport {}\nimport {}\nimport {}\nimport {}\nimport {}", g("D01"), g("Desc"), g("TG"), g("TS"), g("Top"), g("LG1"));
        let mut m = ghdr(p, &imps, "Ctl9", &format!("LRSpectrumFull.NineProbe {} {} {} {} {} {}", g("D01"), g("Desc"), g("TG"), g("TS"), g("Top"), g("LG1")));
        let mut done = 0;
        // task: a mid-size task with a corruptible record
        let mut best: Option<(usize, usize)> = None;
        for (i, t) in e.tasks.iter().enumerate() { if t.nodes >= 30 && t.nodes <= 400 { if let Some(f) = find_corrupt(&t.stream) { best = Some((i, f)); break; } } }
        if let Some((i, f)) = best {
            let (bi, sh) = (f / 256, 16 * (f % 256));
            writeln!(m, "theorem ctl_task_good : allTasks X0 TaskCH TaskSt TaskN (clampT HST HSN) (clampT D1T D1N) {} 1 = true := by decide +kernel", i).unwrap();
            writeln!(m, "def badBlobs : List Nat := (tcOf TaskCH TaskSt TaskN {}).2.set {} (Nat.xor (((tcOf TaskCH TaskSt TaskN {}).2).getD {} 0) (Nat.shiftLeft 1 {}))", i, bi, i, bi, sh).unwrap();
            writeln!(m, "def CHbad : List (List (St × List Nat)) := [[(noH 0, badBlobs)]]").unwrap();
            writeln!(m, "theorem ctl_task_bad : allTasks X0 CHbad [0] 1 (fun _ => clampT HST HSN {}) (clampT D1T D1N) 0 1 = false := by decide +kernel", i).unwrap();
            println!("CTL task {} field {} (blob {} shift {})", i, f, bi, sh); done += 1;
        }
        // a top-level corruption exists even when the top stream has no bound leaf: the first delegation `7 i` whose
        // index i is changed to i xor 1 names a different task state (checked here), so `stEq (H (i xor 1)) s` must fail
        let top_c = find_corrupt(&e.top_stream).or_else(|| find_corrupt_deleg(&e.top_stream, &e.tasks));
        if let Some(f) = top_c {
            let (bi, sh) = (f / 256, 16 * (f % 256));
            writeln!(m, "def badTop : Nat → Nat := fun i => bif Nat.beq i {} then Nat.xor (C0 i) (Nat.shiftLeft 1 {}) else C0 i", bi, sh).unwrap();
            writeln!(m, "theorem ctl_top_bad : checkTree0 X0 badTop (clampT HST HSN) (clampT D1T D1N) = false := by decide +kernel").unwrap();
            println!("CTL top field {}", f); done += 1;
        }
        let mut b1: Option<(usize, usize)> = None;
        for (i, t) in e.trees[1].iter().enumerate() { if let Some(f) = find_corrupt(&t.stream) { b1 = Some((i, f)); break; } }
        if let Some((i, f)) = b1 {
            let (bi, sh) = (f / 256, 16 * (f % 256));
            writeln!(m, "theorem ctl_root1_good : allRootsF X1 (ctT S1T D1N) (clampT D2T D2N) (clampT D1T D1N) {} 1 = true := by decide +kernel", i).unwrap();
            writeln!(m, "def badStr1 : List Nat := (S1T {}).set {} (Nat.xor ((S1T {}).getD {} 0) (Nat.shiftLeft 1 {}))", i, bi, i, bi, sh).unwrap();
            writeln!(m, "theorem ctl_root1_bad : allRootsF X1 (fun _ j => badStr1.getD j 0) (clampT D2T D2N) (fun _ => clampT D1T D1N {}) 0 1 = false := by decide +kernel", i).unwrap();
            println!("CTL level-1 tree {} field {}", i, f); done += 1;
        }
        println!("CTL count {}", done);
        m.push_str(&close("Ctl9")); wr("Ctl9", &m); order.push("Ctl9".into());
    }
    // assembly
    {
        let mut imps = vec![g("D01"), g("D2"), g("Desc"), g("TG"), g("TS"), g("LG1"), g("LG2"), g("Top")];
        for t in &tabmods { imps.push(g(t)); }
        for t in &tkn { imps.push(g(t)); } for t in &lkn[0] { imps.push(g(t)); } for t in &lkn[1] { imps.push(g(t)); }
        let ims = imps.iter().map(|n| format!("import {}", n)).collect::<Vec<_>>().join("\n") + "\nimport LRSpectrumFull.NineSound.DrvSound\nimport LRSpectrumFull.NineSound.DrvFSound\nimport LRSpectrumFull.NineSound.DrvGSound";
        let mut m = ghdr(p, &ims, "PD", &format!("LRSpectrumFull.NineProbe LRSpectrumFull.NineSound LRSpectrumFull.NineSound.Plan9 {} {} {} {} {} {}", g("D01"), g("D2"), g("Desc"), g("TG"), g("TS"), g("LG1")));
        m.push_str(&format!("open {}\n", g("LG2")));
        let ntask: usize = tplan.iter().map(|c| c.1).sum();
        writeln!(m, "theorem tasks_ok : TasksUpTo X0 TaskCH TaskSt TaskN (clampT HST HSN) (clampT D1T D1N) TaskN := by").unwrap();
        writeln!(m, "  have h0 := tasks_base X0 TaskCH TaskSt TaskN (clampT HST HSN) (clampT D1T D1N)").unwrap();
        for (c, &(st, n, _)) in tplan.iter().enumerate() {
            writeln!(m, "  have h{} := tasks_step (m := {}) h{} {}.chk rfl", c + 1, st + n, c, g(&format!("TK{}", c))).unwrap();
        }
        writeln!(m, "  exact h{}\n", tplan.len()).unwrap(); let _ = ntask;
        for (li, lv) in [1usize, 2usize].iter().enumerate() {
            let pl = if li == 0 { &p1 } else { &p2 };
            let (lst, dl, xx, nx) = if *lv == 1 { ("S1T D1N", "(clampT D1T D1N)", "X1", "(clampT D2T D2N)") } else { ("S2T D2N", "(clampT D2T D2N)", "X2", "(fun _ => (0, 0, 0))") };
            let nn = if *lv == 1 { "D1N" } else { "D2N" };
            let nt: usize = pl.iter().map(|c| c.1).sum();
            writeln!(m, "theorem roots{}_ok : RootsUpToF {} (ctT {}) {} {} {} := by", lv, xx, lst, nx, dl, nn).unwrap();
            writeln!(m, "  have h0 := rootsF_base {} (ctT {}) {} {}", xx, lst, nx, dl).unwrap();
            for (c, &(st, n, _)) in pl.iter().enumerate() {
                if c + 1 == pl.len() {
                    assert_eq!(st + n, nt);
                    writeln!(m, "  have h{} := rootsF_step (m := {}) h{} {}.chk (by decide +kernel)", c + 1, nn, c, g(&format!("LK{}_{}", lv, c))).unwrap();
                } else {
                    writeln!(m, "  have h{} := rootsF_step (m := {}) h{} {}.chk rfl", c + 1, st + n, c, g(&format!("LK{}_{}", lv, c))).unwrap();
                }
            }
            writeln!(m, "  exact h{}\n", pl.len()).unwrap();
        }
        writeln!(m, "theorem primeData_{} : PrimeData {} :=\n  primeData_of_partsG {} {} {} {} {} TaskCH TaskSt TaskN HST HSN D1T D2T D1N D2N S1T S2T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)\n    {} {} {} {} tasks_ok roots1_ok roots2_ok",
            p, p, p, format!("{}.X0", g("D01")), format!("{}.X1", g("D01")), format!("{}.X2", g("D2")), format!("{}.C0", g("Top")),
            format!("{}.tableOK9g_X0", g("T0A")), format!("{}.tableOK9g_X1", g("T1A")), format!("{}.tableOK9g_X2", g("T2A")), format!("{}.top_ok", g("Top"))).unwrap();
        m.push_str(&close("PD")); wr("PD", &m); order.push("PD".into());
    }
    fs::write(format!("{}/order.txt", outdir), order.join("\n") + "\n").unwrap();
    println!("WROTE {} modules (order.txt); task chunks {} L1 chunks {} L2 chunks {}", order.len(), tplan.len(), p1.len(), p2.len());
}
fn lean_ctx_old(ns: &str, l: usize, p: usize, lv: &Level) -> String {
    let n = lv.n; let mut s = String::new();
    let lvl = l;
    for j in 1..=n { let mut c = Z; for x in bits(&lv.cov[j]) { sb(&mut c, x); } writeln!(s, "def cb{}_{} : Nat := {}", lvl, j, spread_lit(&c)).unwrap(); }
    // row tree keyed by isolated spread bit
    fn rowt(s: &mut String, lvl: usize, lv: &Level, lo: usize, hi: usize) -> String {
        let name = format!("rw{}_{}_{}", lvl, lo, hi);
        if hi - lo == 1 {
            let x = lo;
            let tc = if lvl >= 2 { spread_lit(&lv.tcls[x]) } else { "(nat_lit 0)".into() };
            let pcl = if lvl >= 1 { spread_lit(&lv.pcls[x]) } else { "(nat_lit 0)".into() };
            writeln!(s, "def {} (_ : Nat) : Nat × Nat × Nat × Nat := ((nat_lit {}), {}, {}, {})", name, x, compact_lit(&lv.cov[x]), pcl, tc).unwrap();
            return name;
        }
        let mid = (lo + hi) / 2; let a = rowt(s, lvl, lv, lo, mid); let b = rowt(s, lvl, lv, mid, hi);
        writeln!(s, "def {} (b : Nat) : Nat × Nat × Nat × Nat := bif Nat.ble {} b then {} b else {} b", name, pow2_16(mid), b, a).unwrap(); name
    }
    let rw = rowt(&mut s, lvl, lv, 1, n + 1);
    fn cjt(s: &mut String, lvl: usize, lo: usize, hi: usize) -> String {
        let name = format!("cj{}_{}_{}", lvl, lo, hi);
        if hi - lo == 1 { writeln!(s, "def {} (_ : Nat) : Nat := cb{}_{}", name, lvl, lo).unwrap(); return name; }
        let mid = (lo + hi) / 2; let a = cjt(s, lvl, lo, mid); let b = cjt(s, lvl, mid, hi);
        writeln!(s, "def {} (j : Nat) : Nat := bif Nat.ble (nat_lit {}) j then {} j else {} j", name, mid, b, a).unwrap(); name
    }
    let cj = cjt(&mut s, lvl, 1, n + 1);
    fn cft(s: &mut String, lvl: usize, lo: usize, hi: usize) -> String {
        let name = format!("cf{}_{}_{}", lvl, lo, hi);
        if hi - lo == 1 { writeln!(s, "def {} (u acc : Nat) : Nat := bif Nat.beq (Nat.land u {}) (nat_lit 0) then acc else Nat.add acc cb{}_{}", name, pow2_lit(lo), lvl, lo).unwrap(); return name; }
        let mid = (lo + hi) / 2; let a = cft(s, lvl, lo, mid); let b = cft(s, lvl, mid, hi);
        writeln!(s, "def {} (u acc : Nat) : Nat := bif Nat.beq (Nat.land u {}) (nat_lit 0) then acc else {} u ({} u acc)", name, maskrange_lit(lo, hi), a, b).unwrap(); name
    }
    let cf = format!("cfRef {} 13 1 ((nat_lit {}) + 1)", cj, n);
    writeln!(s, "def X{} : Ctx := {{ lvl := nat_lit {}, W := nat_lit {}, full := {}, adm := {}, m3 := {}, ones := {}, lowp := {}, lowT := {}, row := {}, cbJ := {}, cntF := {} }}",
        lvl, lvl, n, compact_lit(&lv.full), spread_lit(&lv.adm), spread_lit(&lv.m3), spread_lit_with0(&Z, n), spread_lit(&lv.lowp), spread_lit(&lv.lowt), rw, cj, cf).unwrap();
    let _ = (ns, p);
    s
}

fn lean_ctx_sel(lvl: usize, p: usize, lv: &Level) -> String {
    if std::env::var("TABMODE").map(|v| v == "packed").unwrap_or(false) { lean_ctx_packed(lvl, lv) } else { lean_ctx_old("D", lvl, p, lv) }
}
