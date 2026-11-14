// =====================================================================
// CỜ CARO - AI: MINIMAX + CẮT TỈA ALPHA-BETA (có tối ưu)
// Luật thắng: 4 quân liên tiếp mà KHÔNG đầu nào bị quân địch chặn
//             (tường KHÔNG tính là chặn). Nếu 1 đầu bị chặn thì cần 5 quân.
// =====================================================================
const N = 20; // kích thước bàn cờ (đổi 20 thì chỉnh --cell trong CSS)
const EMPTY = 0,
  HUMAN = 1,
  AI = 2;
const SYMBOL = ["", "X", "O"];

// ---------------- Cấu hình AI ----------------
const TIME_LIMIT = 1500; // ms tối đa cho mỗi nước đi của máy
const MAX_DEPTH = 8; // độ sâu tối đa (đào sâu dần - iterative deepening)
const CAP_ROOT = 18; // số nước tối đa xét ở gốc
const CAP_NODE = 10; // số nước tối đa xét ở mỗi nút trong cây
const RADIUS = 2; // chỉ xét ô cách quân đã đánh <= 2 ô
const TERMINAL = 1e9; // giá trị khi có người thắng

// ---------------- BẢNG ĐIỂM ----------------
// SCORE[số quân liên tiếp][số đầu bị quân địch chặn]
//                   0 đầu bị chặn | 1 đầu bị chặn | 2 đầu bị chặn
const SCORE = [
  [0, 0, 0],
  [10, 2, 0], // 1 quân
  [100, 20, 0], // 2 quân
  [3000, 300, 0], // 3 quân (3 mở: dọa thắng ngay nước sau)
  [100000, 10000, 0], // 4 quân (4 mở = THẮNG; 4 bị chặn 1 đầu = chỉ cần thêm 1 quân là thắng)
  [100000, 100000, 100000], // >= 5 quân = thắng
];
const W_AI = 10; // trọng số điểm của máy
const W_HUMAN = 11; // ưu tiên phòng thủ nhiều hơn 10%

// ---------------- Trạng thái ----------------
const board = new Int8Array(N * N); // 0 trống, 1 = X (người), 2 = O (máy)
const near = new Int16Array(N * N); // đếm số quân nằm trong bán kính RADIUS (để lấy nước ứng viên)
const LINE = new Int8Array(N);
const DR = [0, 1, 1, 1],
  DC = [1, 0, 1, -1]; // ngang, dọc, chéo chính, chéo phụ
let evalScore = 0; // điểm đánh giá toàn bàn cờ (cập nhật dần, dương = có lợi cho máy)
let movesCount = 0;
let turn = HUMAN,
  isGameOver = false,
  lastIdx = -1;

const boardEl = document.getElementById("board");
const statusEl = document.getElementById("status");
const statsEl = document.getElementById("stats");
const cells = [];

// =====================================================================
// PHẦN LOGIC BÀN CỜ + HÀM ĐÁNH GIÁ
// =====================================================================
const inB = (r, c) => r >= 0 && r < N && c >= 0 && c < N;

// Giá trị của đường thẳng đi qua (r,c) theo hướng (dr,dc): cộng điểm từng "đoạn" quân liền nhau
function lineValue(r, c, dr, dc) {
  while (inB(r - dr, c - dc)) {
    r -= dr;
    c -= dc;
  } // lùi về đầu đường
  let n = 0;
  while (inB(r, c)) {
    LINE[n++] = board[r * N + c];
    r += dr;
    c += dc;
  }

  let total = 0,
    i = 0;
  while (i < n) {
    const v = LINE[i];
    if (v === 0) {
      i++;
      continue;
    }
    let j = i;
    while (j + 1 < n && LINE[j + 1] === v) j++;
    const len = j - i + 1,
      opp = 3 - v;

    let blocked = 0; // tường KHÔNG tính là chặn
    if (i > 0 && LINE[i - 1] === opp) blocked++;
    if (j < n - 1 && LINE[j + 1] === opp) blocked++;

    let lo = i,
      hi = j; // khoảng trống còn lại để phát triển
    while (lo > 0 && LINE[lo - 1] !== opp) lo--;
    while (hi < n - 1 && LINE[hi + 1] !== opp) hi++;
    if (hi - lo + 1 >= 4) {
      // đủ chỗ mới có giá trị
      total += (v === AI ? W_AI : -W_HUMAN) * SCORE[Math.min(len, 5)][blocked];
    }
    i = j + 1;
  }
  return total;
}

const dirSum = (r, c) =>
  lineValue(r, c, 0, 1) +
  lineValue(r, c, 1, 0) +
  lineValue(r, c, 1, 1) +
  lineValue(r, c, 1, -1);

// Kiểm tra thắng tại (r,c). wantCells = true thì trả về danh sách ô thắng
function checkWin(r, c, p, wantCells = false) {
  const opp = 3 - p;
  for (let d = 0; d < 4; d++) {
    const dr = DR[d],
      dc = DC[d];
    let f = 0,
      b = 0,
      blocked = 0;
    let rr = r + dr,
      cc = c + dc;
    while (inB(rr, cc) && board[rr * N + cc] === p) {
      f++;
      rr += dr;
      cc += dc;
    }
    if (inB(rr, cc) && board[rr * N + cc] === opp) blocked++;
    rr = r - dr;
    cc = c - dc;
    while (inB(rr, cc) && board[rr * N + cc] === p) {
      b++;
      rr -= dr;
      cc -= dc;
    }
    if (inB(rr, cc) && board[rr * N + cc] === opp) blocked++;
    const cnt = 1 + f + b;
    if (cnt >= 5 || (cnt === 4 && blocked === 0)) {
      if (!wantCells) return true;
      const res = [];
      for (let k = -b; k <= f; k++) res.push((r + dr * k) * N + (c + dc * k));
      return res;
    }
  }
  return false;
}

function updateNear(r, c, delta) {
  for (let dr = -RADIUS; dr <= RADIUS; dr++)
    for (let dc = -RADIUS; dc <= RADIUS; dc++)
      if (inB(r + dr, c + dc)) near[(r + dr) * N + (c + dc)] += delta;
}

// Đặt quân + cập nhật điểm CHỈ trên 4 đường đi qua ô đó (rất nhanh)
function doMove(idx, p) {
  const r = (idx / N) | 0,
    c = idx % N;
  const before = dirSum(r, c);
  board[idx] = p;
  updateNear(r, c, 1);
  const d = dirSum(r, c) - before;
  evalScore += d;
  return d;
}
function undoMove(idx, d) {
  board[idx] = 0;
  updateNear((idx / N) | 0, idx % N, -1);
  evalScore -= d;
}

// =====================================================================
// THUẬT TOÁN AI
// =====================================================================
let nodes = 0,
  pruned = 0,
  deadline = 0,
  timeUp = false;

// Sinh nước đi ứng viên + sắp xếp nước tốt trước (giúp Alpha-Beta cắt tỉa nhiều hơn)
function orderedMoves(p, cap) {
  const opp = 3 - p,
    sign = p === AI ? 1 : -1,
    list = [];
  for (let i = 0; i < N * N; i++) {
    if (board[i] !== 0 || near[i] === 0) continue;
    const r = (i / N) | 0,
      c = i % N;
    const before = dirSum(r, c);
    board[i] = p;
    let key = sign * (dirSum(r, c) - before); // nước này tăng điểm cho p bao nhiêu (tấn công + chặn địch)
    if (checkWin(r, c, p)) key += 1e9; // nước thắng ngay
    board[i] = opp;
    if (checkWin(r, c, opp)) key += 5e8; // nước phải chặn (địch đánh vào đó là thắng)
    board[i] = 0;
    list.push([key, i]);
  }
  list.sort((a, b) => b[0] - a[0]);
  if (list.length && list[0][0] >= 1e9) return [list[0][1]]; // có nước thắng ngay thì chỉ cần nó
  return list.slice(0, cap).map((x) => x[1]);
}

// Minimax + cắt tỉa Alpha-Beta
function search(depth, alpha, beta, maximizing) {
  if ((++nodes & 1023) === 0 && performance.now() > deadline) timeUp = true;
  if (timeUp) return 0;
  if (depth === 0) return evalScore;

  const p = maximizing ? AI : HUMAN;
  const moves = orderedMoves(p, CAP_NODE);
  if (moves.length === 0) return 0; // hết ô -> hòa

  let best = maximizing ? -Infinity : Infinity;
  for (const idx of moves) {
    const d = doMove(idx, p);
    let val;
    if (checkWin((idx / N) | 0, idx % N, p))
      val = maximizing ? TERMINAL + depth : -TERMINAL - depth;
    else val = search(depth - 1, alpha, beta, !maximizing);
    undoMove(idx, d);
    if (timeUp) return 0;

    if (maximizing) {
      if (val > best) best = val;
      if (best > alpha) alpha = best;
    } else {
      if (val < best) best = val;
      if (best < beta) beta = best;
    }
    if (alpha >= beta) {
      pruned++;
      break;
    } // cắt tỉa
  }
  return best;
}

// Đào sâu dần (depth 1,2,3...) đến khi hết thời gian; luôn giữ kết quả của độ sâu hoàn chỉnh gần nhất
function aiChooseMove() {
  const t0 = performance.now();
  nodes = 0;
  pruned = 0;
  timeUp = false;
  deadline = t0 + TIME_LIMIT;

  if (movesCount === 0)
    return { idx: (N >> 1) * N + (N >> 1), depth: 0, ms: 0 };
  let rootMoves = orderedMoves(AI, CAP_ROOT);
  if (rootMoves.length === 0) return null;
  let best = rootMoves[0],
    reached = 0;

  for (let depth = 1; depth <= MAX_DEPTH; depth++) {
    let alpha = -Infinity,
      curBest = null,
      curVal = -Infinity;
    for (const idx of rootMoves) {
      const d = doMove(idx, AI);
      const val = checkWin((idx / N) | 0, idx % N, AI)
        ? TERMINAL + depth
        : search(depth - 1, alpha, Infinity, false);
      undoMove(idx, d);
      if (timeUp) break;
      if (val > curVal) {
        curVal = val;
        curBest = idx;
      }
      if (val > alpha) alpha = val;
    }
    if (timeUp || curBest === null) break;
    best = curBest;
    reached = depth;
    rootMoves = [best, ...rootMoves.filter((m) => m !== best)]; // nước tốt nhất xét trước ở vòng sau
    if (Math.abs(curVal) >= TERMINAL) break; // đã thấy thắng/thua bắt buộc
  }
  return { idx: best, depth: reached, ms: Math.round(performance.now() - t0) };
}

// =====================================================================
// PHẦN GIAO DIỆN + LUỒNG GAME
// =====================================================================
function initGame() {
  board.fill(0);
  near.fill(0);
  evalScore = 0;
  movesCount = 0;
  turn = HUMAN;
  isGameOver = false;
  lastIdx = -1;
  document.getElementById("title").innerText = `Cờ Caro ${N}x${N}`;
  boardEl.style.setProperty("--n", N);
  boardEl.innerHTML = "";
  cells.length = 0;
  for (let i = 0; i < N * N; i++) {
    const el = document.createElement("div");
    el.className = "cell";
    el.dataset.i = i;
    boardEl.appendChild(el);
    cells.push(el);
  }
  setStatus("Lượt của: Bạn (X)", "#1f5fbf");
  statsEl.innerText = "";
}

function setStatus(text, color) {
  statusEl.innerText = text;
  statusEl.style.color = color;
}

function makeMove(idx, p) {
  doMove(idx, p);
  movesCount++;
  if (lastIdx >= 0) cells[lastIdx].classList.remove("last");
  lastIdx = idx;
  cells[idx].innerText = SYMBOL[p];
  cells[idx].classList.add(SYMBOL[p].toLowerCase(), "last");
}

function endIfOver(idx, p) {
  const win = checkWin((idx / N) | 0, idx % N, p, true);
  if (win) {
    isGameOver = true;
    win.forEach((i) => cells[i].classList.add("win"));
    if (p === HUMAN) setStatus("🎉 Bạn (X) đã CHIẾN THẮNG!", "#1f5fbf");
    else setStatus("🤖 Máy (O) đã CHIẾN THẮNG!", "#c8352b");
    return true;
  }
  if (movesCount === N * N) {
    isGameOver = true;
    setStatus("🤝 Trận đấu HÒA!", "#555");
    return true;
  }
  return false;
}

function humanMove(idx) {
  if (isGameOver || turn !== HUMAN || board[idx] !== 0) return;
  makeMove(idx, HUMAN);
  if (endIfOver(idx, HUMAN)) return;
  turn = AI;
  setStatus("🤖 Máy (O) đang suy nghĩ...", "#c8352b");
  setTimeout(aiMove, 50); // cho trình duyệt kịp vẽ quân X trước khi máy tính toán
}

function aiMove() {
  const res = aiChooseMove();
  if (!res) return endIfOver(0, AI);
  makeMove(res.idx, AI);
  statsEl.innerText = `Độ sâu đạt: ${res.depth} | Nút duyệt: ${nodes} | Lần cắt tỉa: ${pruned} | ${res.ms} ms | Điểm: ${evalScore}`;
  if (endIfOver(res.idx, AI)) return;
  turn = HUMAN;
  setStatus("Lượt của: Bạn (X)", "#1f5fbf");
}

boardEl.addEventListener("click", (e) => {
  const el = e.target.closest(".cell");
  if (el) humanMove(parseInt(el.dataset.i));
});
document.getElementById("reset-btn").addEventListener("click", initGame);
initGame();
