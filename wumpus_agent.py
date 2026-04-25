"""
AI 2002 - Assignment 6, Question 6
Wumpus World - Knowledge Based Agent
Web App using Python (no external libraries needed)

"""

import random
import json
import os
from http.server import HTTPServer, BaseHTTPRequestHandler


# ================================================================
# PART 1: KNOWLEDGE BASE
# ================================================================

class KnowledgeBase:
    

    def __init__(self):
        self.facts       = set()   
        self.clauses     = []     
        self.clause_set  = set()  

    def tell(self, fact):
        """Add a new fact to the KB."""
        if fact not in self.facts:
            self.facts.add(fact)
            self._add_clause([fact])  

    def ask(self, fact):
        """Return True if fact is in KB."""
        return fact in self.facts

    def _add_clause(self, clause):
        """Add a CNF clause (list of literals). Skip duplicates."""
        key = "|".join(sorted(clause))
        if key not in self.clause_set:
            self.clause_set.add(key)
            self.clauses.append(list(clause))

    @staticmethod
    def negate(literal):
        """Flip sign of a literal.  pit -> ~pit,   ~pit -> pit"""
        return literal[1:] if literal.startswith("~") else "~" + literal

    # -----------------------------------------------------------
    # 
    # If has_breeze=True:
    #   Tell KB: B is true, and at least one neighbour is a pit
    # If has_breeze=False:
    #   Tell KB: ~B is true, and NO neighbour is a pit
    # -----------------------------------------------------------
    def tell_breeze_rule(self, r, c, neighbours, has_breeze):
        B        = f"breeze_{r}_{c}"
        pit_lits = [f"pit_{nr}_{nc}" for nr, nc in neighbours]

        if has_breeze:
            self.tell(B)
            # CNF clause: ~B OR pit_n1 OR pit_n2 OR ...
            self._add_clause([f"~{B}"] + pit_lits)
        else:
            self.tell(f"~{B}")
            # No breeze -> every neighbour is definitely NOT a pit
            for p in pit_lits:
                self.tell(f"~{p}")
                self._add_clause([B, f"~{p}"])  # CNF: B OR ~pit

        # Each pit neighbour implies breeze: ~pit OR B
        for p in pit_lits:
            self._add_clause([f"~{p}", B])

    # -----------------------------------------------------------
    # TELL Biconditional Stench Rule (same logic, for wumpus)
    # -----------------------------------------------------------
    def tell_stench_rule(self, r, c, neighbours, has_stench):
        S      = f"stench_{r}_{c}"
        w_lits = [f"wumpus_{nr}_{nc}" for nr, nc in neighbours]

        if has_stench:
            self.tell(S)
            self._add_clause([f"~{S}"] + w_lits)
        else:
            self.tell(f"~{S}")
            for w in w_lits:
                self.tell(f"~{w}")
                self._add_clause([S, f"~{w}"])

        for w in w_lits:
            self._add_clause([f"~{w}", S])

    # -----------------------------------------------------------
    # RESOLUTION REFUTATION
    #
    # To PROVE a goal, we:
    #   1. Take all CNF clauses from the KB
    #   2. Add [NOT goal] as a new unit clause
    #   3. Repeatedly resolve pairs of clauses:
    #      - Find literal L in clause A, and ~L in clause B
    #      - Resolvent = (A without L) UNION (B without ~L)
    #   4. If resolvent is EMPTY -> contradiction -> GOAL IS PROVED
    #   5. If no new clauses can be made -> cannot prove goal
    # -----------------------------------------------------------
    def resolution_refutation(self, goal, max_steps=100):
        neg_goal = self.negate(goal)
        clauses = [list(c) for c in self.clauses]
        clauses.append([neg_goal])

        log   = [f"Goal: {goal}", f"Added negated goal: [{neg_goal}]"]
        steps = 0

        changed = True
        while changed and steps < max_steps:
            changed = False
            n = len(clauses)

            for i in range(n):
                for j in range(i + 1, n):
                    ci = clauses[i]
                    cj = clauses[j]

                    # Look for complementary literal (L in ci, ~L in cj)
                    for lit in ci:
                        neg_lit = self.negate(lit)
                        if neg_lit not in cj:
                            continue

                        # Build resolvent: merge both clauses minus the pair
                        resolvent = list(set(
                            [l for l in ci if l != lit] +
                            [l for l in cj if l != neg_lit]
                        ))
                        steps += 1

                        # EMPTY CLAUSE = contradiction = GOAL PROVED!
                        if len(resolvent) == 0:
                            log.append(f"Step {steps}: Resolve {ci} + {cj} on [{lit}]")
                            log.append("=> Empty clause! CONTRADICTION found.")
                            log.append(f"=> PROVED: {goal}")
                            return True, log, steps

                        # Discard tautologies (has both X and ~X)
                        if any(self.negate(l) in resolvent for l in resolvent):
                            steps -= 1
                            continue

                        # Add if not already in working set
                        key = "|".join(sorted(resolvent))
                        if key not in self.clause_set:
                            log.append(f"Step {steps}: {ci} + {cj} on [{lit}] => {resolvent}")
                            self.clause_set.add(key)
                            clauses.append(resolvent)
                            changed = True

                        break   # one resolution per clause pair

        log.append(f"No contradiction found. Cannot prove: {goal}")
        return False, log, steps


# ================================================================
# PART 2: WORLD HELPERS
# ================================================================

def get_neighbours(r, c, rows, cols):
    """Return valid up/down/left/right neighbours of (r,c)."""
    result = []
    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
        nr, nc = r + dr, c + dc
        if 0 <= nr < rows and 0 <= nc < cols:
            result.append((nr, nc))
    return result


def create_world(rows, cols, num_pits):
    """Randomly place pits, one wumpus, and gold. (0,0) is always safe."""
    all_cells = [
        (r, c) for r in range(rows) for c in range(cols)
        if not (r == 0 and c == 0)
    ]
    random.shuffle(all_cells)
    num_pits   = min(num_pits, len(all_cells) - 2)
    pits       = set(f"{r}_{c}" for r, c in all_cells[:num_pits])
    wumpus     = all_cells[num_pits]
    gold       = all_cells[num_pits + 1]
    return pits, wumpus, gold


def get_percepts(r, c, pits, wumpus, rows, cols):
    """Return (breeze, stench) for cell (r,c)."""
    nb     = get_neighbours(r, c, rows, cols)
    breeze = any(f"{nr}_{nc}" in pits for nr, nc in nb)
    stench = any(nr == wumpus[0] and nc == wumpus[1] for nr, nc in nb)
    return breeze, stench


# ================================================================
# PART 3: GAME CLASS
# ================================================================

class Game:
    def __init__(self, rows, cols, num_pits):
        self.rows     = rows
        self.cols     = cols
        self.num_pits = num_pits

        # Create the hidden world
        self.pits, self.wumpus, self.gold = create_world(rows, cols, num_pits)

        # Agent state
        self.agent    = (0, 0)
        self.visited  = {"0_0"}
        self.safe     = {"0_0"}
        self.danger   = set()
        self.frontier = [(0, 0)]     # cells queued to visit

        # Knowledge Base
        self.kb = KnowledgeBase()
        self.kb.tell("safe_0_0")
        self.kb.tell("~pit_0_0")
        self.kb.tell("~wumpus_0_0")

        # Metrics
        self.steps           = 0
        self.inference_steps = 0

        # Game status
        self.alive = True
        self.won   = False
        self.stuck = False

        # Logs
        self.agent_log      = ["Episode started. Agent at (0,0)."]
        self.proof_log      = []
        self.percepts       = []
        self.percept_cache  = {}    # key -> {breeze, stench}

        # Process starting cell
        self._visit_cell(0, 0)

    # -----------------------------------------------------------
    def step(self):
        """Move agent one step to the next queued safe cell."""
        if not self.alive or self.won or self.stuck:
            return

        # Find next unvisited safe cell from frontier
        next_cell = None
        while self.frontier:
            candidate = self.frontier.pop(0)
            cr, cc    = candidate
            ckey      = f"{cr}_{cc}"
            if ckey not in self.visited and ckey in self.safe:
                next_cell = candidate
                break

        if next_cell is None:
            self.stuck = True
            self.agent_log.append("No safe cells left. Agent is STUCK.")
            return

        self.agent  = next_cell
        self.steps += 1
        self._visit_cell(next_cell[0], next_cell[1])

    # -----------------------------------------------------------
    def _visit_cell(self, r, c):
        """
        Core logic when agent enters cell (r,c):
          1. Mark visited
          2. Check for death / gold
          3. Get percepts
          4. Tell KB the biconditional rules (convert to CNF)
          5. Run Resolution Refutation on each neighbour
          6. Add safe neighbours to frontier
        """
        key = f"{r}_{c}"
        self.visited.add(key)
        self.safe.add(key)
        self.kb.tell(f"visited_{r}_{c}")
        self.kb.tell(f"safe_{r}_{c}")

        # ── Check death ──────────────────────────────────────
        if key in self.pits:
            self.alive = False
            self.agent_log.append(f"Agent fell into PIT at ({r},{c})! GAME OVER.")
            self.percepts = []
            return

        if r == self.wumpus[0] and c == self.wumpus[1]:
            self.alive = False
            self.agent_log.append(f"Agent eaten by WUMPUS at ({r},{c})! GAME OVER.")
            self.percepts = []
            return

        # ── Check gold ───────────────────────────────────────
        if r == self.gold[0] and c == self.gold[1]:
            self.won = True
            self.agent_log.append(f"GOLD found at ({r},{c})! YOU WIN!")
            self.percepts = ["Glitter"]
            return

        # ── Get percepts ─────────────────────────────────────
        breeze, stench = get_percepts(r, c, self.pits, self.wumpus,
                                      self.rows, self.cols)
        self.percepts = []
        if breeze: self.percepts.append("Breeze")
        if stench: self.percepts.append("Stench")

        self.percept_cache[key] = {"breeze": breeze, "stench": stench}
        self.agent_log.append(
            f"At ({r},{c}) | Percepts: {self.percepts or ['None']}"
        )

        # ── Tell KB biconditional percept rules ──────────────
        nb = get_neighbours(r, c, self.rows, self.cols)
        self.kb.tell_breeze_rule(r, c, nb, breeze)
        self.kb.tell_stench_rule(r, c, nb, stench)
        self.inference_steps += 1

        # ── Run Resolution on each unvisited neighbour ────────
        new_proof_log = []
        for nr, nc in nb:
            nkey = f"{nr}_{nc}"
            if nkey in self.visited:
                continue

            # ASK KB: is (nr,nc) safe?  Prove ~pit AND ~wumpus
            pit_ok, pit_log, _ = self.kb.resolution_refutation(f"~pit_{nr}_{nc}")
            w_ok,   w_log,   _ = self.kb.resolution_refutation(f"~wumpus_{nr}_{nc}")
            self.inference_steps += 1

            new_proof_log += [f"--- Checking ({nr},{nc}) ---"] + pit_log + w_log

            if pit_ok and w_ok:
                # SAFE: add to KB and queue for visiting
                self.kb.tell(f"safe_{nr}_{nc}")
                self.safe.add(nkey)
                self.agent_log.append(f"  Inferred SAFE: ({nr},{nc})")
                if (nr, nc) not in self.frontier:
                    self.frontier.append((nr, nc))
            else:
                # Try to confirm it is definitely dangerous
                pit_danger, _, _ = self.kb.resolution_refutation(f"pit_{nr}_{nc}")
                w_danger,   _, _ = self.kb.resolution_refutation(f"wumpus_{nr}_{nc}")
                if pit_danger or w_danger:
                    self.danger.add(nkey)
                    self.agent_log.append(f"  Confirmed DANGER: ({nr},{nc})")

        self.proof_log = new_proof_log

    # -----------------------------------------------------------
    def to_dict(self):
        """Convert game state to a JSON-serialisable dictionary."""
        grid = []
        for r in range(self.rows):
            for c in range(self.cols):
                key = f"{r}_{c}"
                pc  = self.percept_cache.get(key, {})
                grid.append({
                    "r":       r,
                    "c":       c,
                    "visited": key in self.visited,
                    "safe":    key in self.safe,
                    "danger":  key in self.danger,
                    "agent":   self.agent == (r, c),
                    "pit":     key in self.pits,
                    "wumpus":  r == self.wumpus[0] and c == self.wumpus[1],
                    "gold":    r == self.gold[0]   and c == self.gold[1],
                    "breeze":  pc.get("breeze", False),
                    "stench":  pc.get("stench", False),
                })
        return {
            "rows":            self.rows,
            "cols":            self.cols,
            "grid":            grid,
            "steps":           self.steps,
            "inference_steps": self.inference_steps,
            "kb_facts":        len(self.kb.facts),
            "safe_count":      len(self.safe),
            "frontier_size":   len(self.frontier),
            "alive":           self.alive,
            "won":             self.won,
            "stuck":           self.stuck,
            "percepts":        self.percepts,
            "agent_log":       self.agent_log[-30:],
            "proof_log":       self.proof_log[-50:],
        }


# ================================================================
# PART 4: WEB INTERFACE (HTML sent to browser)
# ================================================================

HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>Wumpus World Agent</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0d1117;color:#c9d1d9;font-family:'Courier New',monospace;padding:16px}

h1{color:#58a6ff;text-align:center;font-size:1.5rem;margin-bottom:4px}
.sub{text-align:center;color:#6e7681;font-size:.75rem;margin-bottom:18px}

/* Controls */
.controls{display:flex;flex-wrap:wrap;gap:10px;align-items:flex-end;
  background:#161b22;border:1px solid #30363d;border-radius:8px;padding:14px;margin-bottom:16px}
.ctrl label{display:block;font-size:.62rem;color:#6e7681;margin-bottom:3px;text-transform:uppercase}
.ctrl input[type=number]{width:65px;background:#0d1117;border:1px solid #30363d;color:#58a6ff;
  font-family:inherit;font-size:.95rem;padding:5px 8px;border-radius:5px;outline:none}
.ctrl input[type=number]:focus{border-color:#58a6ff}
.speed-ctrl{display:flex;align-items:center;gap:8px;font-size:.65rem;color:#6e7681}
.speed-ctrl input[type=range]{accent-color:#58a6ff;width:110px}

/* Buttons */
.btn{padding:7px 18px;border:none;border-radius:5px;font-family:inherit;
  font-size:.8rem;font-weight:bold;cursor:pointer}
.btn:disabled{opacity:.35;cursor:not-allowed}
.btn-blue  {background:#1f6feb;color:#fff}
.btn-green {background:#238636;color:#fff}
.btn-gray  {background:#21262d;color:#c9d1d9;border:1px solid #30363d}
.btn-orange{background:#9e6a03;color:#fff}

/* Layout */
.layout{display:grid;grid-template-columns:1fr 310px;gap:14px}
@media(max-width:820px){.layout{grid-template-columns:1fr}}

/* Status bar */
.status{text-align:center;padding:8px 14px;border-radius:6px;font-size:.78rem;
  margin-bottom:10px;background:#0d1117;border:1px solid #30363d;color:#58a6ff}
.status.win  {background:#0a2a1a;border-color:#2ea043;color:#3fb950}
.status.lose {background:#2a0d0d;border-color:#f85149;color:#f85149}
.status.stuck{background:#2a1a00;border-color:#d29922;color:#d29922}

/* Grid */
.grid-wrap{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:12px}
#grid{display:grid;gap:4px;margin-bottom:10px}
.cell{aspect-ratio:1;border-radius:6px;border:1px solid #30363d;min-height:50px;
  display:flex;flex-direction:column;align-items:center;justify-content:center;
  position:relative;transition:background .25s,border-color .25s;overflow:hidden}
.cell .coord{position:absolute;top:2px;left:3px;font-size:.38rem;color:#484f58}
.cell .icon {font-size:1.1rem;line-height:1}
.cell .lbl  {font-size:.45rem;margin-top:1px;opacity:.85}
.cell .perc {position:absolute;bottom:2px;right:3px;font-size:.4rem;color:#d29922}

/* Cell states - Green=Safe, Gray=Unknown, Red=Danger */
.c-unknown{background:#161b22}
.c-visited{background:#0d2137;border-color:#1f4a7a}
.c-safe   {background:#0a2a1a;border-color:#2ea04350}
.c-danger {background:#2a0d0d;border-color:#f8514966}
.c-agent  {background:#0d2a0d;border-color:#3fb950;box-shadow:0 0 10px #3fb95050}

/* Legend */
.legend{display:flex;flex-wrap:wrap;gap:10px;font-size:.6rem;color:#6e7681}
.leg-item{display:flex;align-items:center;gap:4px}
.leg-dot{width:10px;height:10px;border-radius:3px;border:1px solid}

/* Right panel cards */
.card{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:12px;margin-bottom:12px}
.card h3{font-size:.6rem;text-transform:uppercase;letter-spacing:.1em;color:#6e7681;
  margin-bottom:10px;padding-bottom:6px;border-bottom:1px solid #30363d}

/* Metrics */
.metrics{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.metric{background:#0d1117;border:1px solid #30363d;border-radius:6px;padding:8px;text-align:center}
.metric .val{font-size:1.5rem;font-weight:bold;color:#58a6ff;line-height:1}
.metric .lbl{font-size:.5rem;color:#6e7681;margin-top:3px;text-transform:uppercase}
.metric.green  .val{color:#3fb950}
.metric.orange .val{color:#d29922}

/* Percept tags */
.percepts{display:flex;flex-wrap:wrap;gap:5px;min-height:26px}
.tag{padding:2px 10px;border-radius:12px;font-size:.65rem;font-weight:bold}
.tag.breeze {background:#051d40;color:#58a6ff;border:1px solid #1f6feb}
.tag.stench {background:#2d1505;color:#d29922;border:1px solid #9e6a03}
.tag.glitter{background:#2a2200;color:#f0e68c;border:1px solid #b8960c}
.tag.none   {background:#21262d;color:#6e7681;border:1px solid #30363d}

/* Log boxes */
.log-box{background:#0d1117;border:1px solid #30363d;border-radius:5px;
  padding:8px;height:150px;overflow-y:auto;font-size:.6rem;line-height:1.9}
.l-safe {color:#3fb950} .l-warn{color:#d29922}
.l-dead {color:#f85149} .l-info{color:#58a6ff} .l-plain{color:#6e7681}

.proof-box{background:#0d1117;border:1px solid #30363d;border-radius:5px;
  padding:8px;height:130px;overflow-y:auto;font-size:.57rem;line-height:1.9;color:#6e7681}
.proved{color:#3fb950;font-weight:bold} .failed{color:#d29922}
.pstep {color:#c9d1d9}                  .psep  {color:#30363d}
</style>
</head>
<body>

<h1>Wumpus World &mdash; Logic Agent</h1>
<p class="sub">Knowledge-Based Agent &bull; Propositional Logic &bull; Resolution Refutation &bull; CNF Inference Engine</p>

<!-- Controls bar -->
<div class="controls">
  <div class="ctrl"><label>Rows</label><input id="in-rows" type="number" value="4" min="3" max="8"/></div>
  <div class="ctrl"><label>Cols</label><input id="in-cols" type="number" value="4" min="3" max="8"/></div>
  <div class="ctrl"><label>Pits</label> <input id="in-pits" type="number" value="2" min="1" max="6"/></div>
  <div class="ctrl speed-ctrl">
    <label>Speed</label>
    <input type="range" id="speed" min="200" max="2000" value="800"/>
    <span id="speed-lbl">800ms</span>
  </div>
  <button class="btn btn-blue"   id="btn-new"    >New Episode</button>
  <button class="btn btn-green"  id="btn-step"   disabled>Step</button>
  <button class="btn btn-gray"   id="btn-auto"   disabled>Auto Run</button>
  <button class="btn btn-orange" id="btn-reveal" disabled>Reveal All</button>
</div>

<!-- Main layout -->
<div class="layout">

  <!-- LEFT: Grid -->
  <div>
    <div id="status" class="status">Click "New Episode" to start.</div>
    <div class="grid-wrap">
      <div id="grid"></div>
      <div class="legend">
        <div class="leg-item"><div class="leg-dot" style="background:#0d2a0d;border-color:#3fb950"></div>Agent</div>
        <div class="leg-item"><div class="leg-dot" style="background:#0a2a1a;border-color:#2ea043"></div>Safe</div>
        <div class="leg-item"><div class="leg-dot" style="background:#0d2137;border-color:#1f4a7a"></div>Visited</div>
        <div class="leg-item"><div class="leg-dot" style="background:#161b22;border-color:#30363d"></div>Unknown</div>
        <div class="leg-item"><div class="leg-dot" style="background:#2a0d0d;border-color:#f85149"></div>Danger</div>
      </div>
    </div>
  </div>

  <!-- RIGHT: Dashboard -->
  <div>

    <div class="card">
      <h3>Real-Time Metrics</h3>
      <div class="metrics">
        <div class="metric">          <div class="val" id="m-steps">0</div><div class="lbl">Agent Steps</div></div>
        <div class="metric orange">   <div class="val" id="m-infer">0</div><div class="lbl">Inference Steps</div></div>
        <div class="metric green">    <div class="val" id="m-safe" >0</div><div class="lbl">Safe Cells</div></div>
        <div class="metric">          <div class="val" id="m-kb"   >0</div><div class="lbl">KB Facts</div></div>
      </div>
    </div>

    <div class="card">
      <h3>Current Percepts</h3>
      <div class="percepts" id="percepts"><span class="tag none">-</span></div>
    </div>

    <div class="card">
      <h3>Resolution Proof Log</h3>
      <div class="proof-box" id="proof-box">No proof run yet.</div>
    </div>

    <div class="card">
      <h3>Agent Log</h3>
      <div class="log-box" id="log-box"></div>
    </div>

  </div>
</div><!-- layout -->

<script>
let revealed  = false;
let autoTimer = null;

// Call Python server API
async function api(path, data={}) {
  const res = await fetch(path, {
    method: 'POST',
    headers: {'Content-Type':'application/json'},
    body: JSON.stringify(data)
  });
  return res.json();
}

async function newGame() {
  stopAuto();
  revealed = false;
  document.getElementById('btn-reveal').textContent = 'Reveal All';
  const s = await api('/new', {
    rows: +document.getElementById('in-rows').value || 4,
    cols: +document.getElementById('in-cols').value || 4,
    pits: +document.getElementById('in-pits').value || 2,
  });
  render(s);
  document.getElementById('btn-step').disabled   = false;
  document.getElementById('btn-auto').disabled   = false;
  document.getElementById('btn-reveal').disabled = false;
}

async function doStep() {
  const s = await api('/step');
  render(s);
  if (!s.alive || s.won || s.stuck) {
    stopAuto();
    document.getElementById('btn-step').disabled = true;
    document.getElementById('btn-auto').disabled = true;
  }
}

function render(s) {
  renderGrid(s); renderMetrics(s); renderPercepts(s);
  renderStatus(s); renderLog(s); renderProof(s);
}

function renderGrid(s) {
  const gc = document.getElementById('grid');
  gc.style.gridTemplateColumns = `repeat(${s.cols}, 1fr)`;
  gc.innerHTML = '';

  // Sort so row 0 is at bottom, highest row at top (like coordinate system)
  const cells = [...s.grid].sort((a,b) => b.r - a.r || a.c - b.c);

  for (const cell of cells) {
    const div = document.createElement('div');
    div.className = 'cell';

    // Choose background color class
    if (cell.agent) {
      div.classList.add('c-agent');
    } else if (revealed && (cell.pit || cell.wumpus)) {
      div.classList.add('c-danger');
    } else if (cell.danger) {
      div.classList.add('c-danger');
    } else if (cell.visited) {
      div.classList.add('c-visited');
    } else if (cell.safe) {
      div.classList.add('c-safe');
    } else {
      div.classList.add('c-unknown');
    }

    // Coordinate label top-left
    const co = document.createElement('div');
    co.className = 'coord';
    co.textContent = `${cell.r},${cell.c}`;
    div.appendChild(co);

    // Main icon and label
    let icon = '', lbl = '';
    if (cell.agent)                                  { icon = '🤖'; lbl = 'AGENT'; }
    else if (revealed && cell.pit)                   { icon = '🕳️'; lbl = 'PIT'; }
    else if (revealed && cell.wumpus)                { icon = '👹'; lbl = 'WUMPUS'; }
    else if (revealed && cell.gold && !cell.visited) { icon = '💰'; lbl = 'GOLD'; }
    else if (cell.danger && !revealed)               { icon = '⚠️'; lbl = 'DANGER'; }
    else if (cell.visited)                           { icon = '·'; }
    else if (cell.safe)                              { icon = '✓'; lbl = 'SAFE'; }

    if (icon) {
      const ic = document.createElement('div'); ic.className='icon'; ic.textContent=icon; div.appendChild(ic);
    }
    if (lbl) {
      const lb = document.createElement('div'); lb.className='lbl'; lb.textContent=lbl; div.appendChild(lb);
    }

    // Show B (breeze) / S (stench) indicator on visited cells
    if (cell.visited && !cell.agent) {
      const p = (cell.breeze ? 'B' : '') + (cell.stench ? 'S' : '');
      if (p) {
        const pd = document.createElement('div'); pd.className='perc'; pd.textContent=p; div.appendChild(pd);
      }
    }

    gc.appendChild(div);
  }
}

function renderMetrics(s) {
  document.getElementById('m-steps').textContent = s.steps;
  document.getElementById('m-infer').textContent = s.inference_steps;
  document.getElementById('m-safe').textContent  = s.safe_count;
  document.getElementById('m-kb').textContent    = s.kb_facts;
}

function renderPercepts(s) {
  const pl = document.getElementById('percepts');
  pl.innerHTML = '';
  if (!s.percepts.length) {
    pl.innerHTML = '<span class="tag none">None - All Clear</span>'; return;
  }
  for (const p of s.percepts) {
    const sp = document.createElement('span');
    sp.className = 'tag ' + p.toLowerCase();
    sp.textContent = p;
    pl.appendChild(sp);
  }
}

function renderStatus(s) {
  const el = document.getElementById('status');
  el.className = 'status';
  if (!s.alive)   { el.classList.add('lose');  el.textContent = '💀 Agent died! Game Over.'; }
  else if (s.won) { el.classList.add('win');   el.textContent = `🏆 Gold found in ${s.steps} steps! Victory!`; }
  else if (s.stuck){ el.classList.add('stuck'); el.textContent = '⚡ No safe path. Agent stuck.'; }
  else            { el.textContent = `Running - Frontier: ${s.frontier_size} cells queued`; }
}

function renderLog(s) {
  const lb = document.getElementById('log-box');
  lb.innerHTML = '';
  for (const line of s.agent_log) {
    const d = document.createElement('div');
    if (line.includes('GOLD') || line.includes('SAFE'))      d.className = 'l-safe';
    else if (line.includes('GAME OVER') || line.includes('PIT') || line.includes('eaten')) d.className = 'l-dead';
    else if (line.includes('DANGER') || line.includes('STUCK')) d.className = 'l-warn';
    else if (line.includes('At (') || line.includes('started')) d.className = 'l-info';
    else d.className = 'l-plain';
    d.textContent = line;
    lb.appendChild(d);
  }
  lb.scrollTop = lb.scrollHeight;
}

function renderProof(s) {
  const pb = document.getElementById('proof-box');
  pb.innerHTML = '';
  for (const line of s.proof_log) {
    const d = document.createElement('div');
    if (line.includes('PROVED') || line.includes('contradiction')) d.className = 'proved';
    else if (line.includes('Cannot') || line.includes('CANNOT'))   d.className = 'failed';
    else if (line.startsWith('---'))                               d.className = 'psep';
    else                                                           d.className = 'pstep';
    d.textContent = line;
    pb.appendChild(d);
  }
  pb.scrollTop = pb.scrollHeight;
}

function startAuto() {
  if (autoTimer) return;
  document.getElementById('btn-auto').textContent = 'Stop';
  const delay = () => +document.getElementById('speed').value || 800;
  async function tick() {
    await doStep();
    if (!document.getElementById('btn-step').disabled)
      autoTimer = setTimeout(tick, delay());
  }
  autoTimer = setTimeout(tick, delay());
}

function stopAuto() {
  if (autoTimer) { clearTimeout(autoTimer); autoTimer = null; }
  document.getElementById('btn-auto').textContent = 'Auto Run';
}

document.getElementById('btn-new').addEventListener('click', newGame);
document.getElementById('btn-step').addEventListener('click', () => { stopAuto(); doStep(); });
document.getElementById('btn-auto').addEventListener('click', () => autoTimer ? stopAuto() : startAuto());
document.getElementById('btn-reveal').addEventListener('click', async () => {
  revealed = !revealed;
  document.getElementById('btn-reveal').textContent = revealed ? 'Hide' : 'Reveal All';
  renderGrid(await api('/state'));
});
document.getElementById('speed').addEventListener('input', function() {
  document.getElementById('speed-lbl').textContent = this.value + 'ms';
});
</script>
</body>
</html>
"""


# ================================================================
# PART 5: HTTP SERVER
# ================================================================

game_instance = None   # holds the active Game object


class Handler(BaseHTTPRequestHandler):

    # Serve the HTML page on GET /
    def do_GET(self):
        if self.path == '/':
            body = HTML.encode()
            self.send_response(200)
            self.send_header('Content-Type', 'text/html')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        else:
            self.send_response(404)
            self.end_headers()

    # Handle game API calls on POST
    def do_POST(self):
        global game_instance

        length = int(self.headers.get('Content-Length', 0))
        body   = json.loads(self.rfile.read(length) or b'{}')

        if self.path == '/new':
            rows = max(3, min(8, int(body.get('rows', 4))))
            cols = max(3, min(8, int(body.get('cols', 4))))
            pits = max(1, min(6, int(body.get('pits', 2))))
            game_instance = Game(rows, cols, pits)

        elif self.path == '/step':
            if game_instance:
                game_instance.step()

        elif self.path == '/state':
            pass   # just return current state

        response = game_instance.to_dict() if game_instance else {}
        data     = json.dumps(response).encode()

        self.send_response(200)
        self.send_header('Content-Type', 'application/json')
        self.send_header('Content-Length', str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def log_message(self, format, *args):
        pass   # silence server request logs


# ================================================================
# PART 6: MAIN - start the server
# ================================================================

if __name__ == '__main__':
    PORT   = int(os.environ.get('PORT', 3000))
    server = HTTPServer(('', PORT), Handler)

    print("=" * 50)
    print("  Wumpus World Logic Agent")
    print(f"  Open browser at: http://localhost:{PORT}")
    print("  Press Ctrl+C to stop")
    print("=" * 50)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServer stopped.")
# World Creation Module
# Resolution Refutation Added
# Web interface added
