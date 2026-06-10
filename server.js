const crypto = require("crypto");
const fs = require("fs");
const http = require("http");
const path = require("path");
const { URL } = require("url");

const rooms = new Map();
const ROOM_CODE_LENGTH = 6;
const MIN_TOTAL_PLAYERS = 2;
const MAX_TOTAL_PLAYERS = 6;
const MIN_BOARD_SIDE = 3;
const MAX_BOARD_SIDE = 12;
const THEMES = new Set(["classic", "light", "neon", "mural", "ocean"]);
const BOT_THINK_TIME_MS = 650;
const BOT_BASE_NAME = "Thankan";
const DEFAULT_MOVE_TIME_SECONDS = 12;
const MIN_MOVE_TIME_SECONDS = 3;
const MAX_MOVE_TIME_SECONDS = 60;
const DIRECTIONS = [
  [0, 1],
  [1, 0],
  [1, 1],
  [1, -1]
];
const PUBLIC_DIR = path.resolve(__dirname);

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function normalizePlayerName(name) {
  const cleaned = String(name || "")
    .trim()
    .replace(/\s+/g, " ")
    .slice(0, 24);

  return cleaned || "Player";
}

function normalizeRoomCode(code) {
  return String(code || "")
    .trim()
    .toUpperCase()
    .replace(/[^A-Z0-9]/g, "")
    .slice(0, ROOM_CODE_LENGTH);
}

function hashPassword(password) {
  return crypto
    .createHash("sha256")
    .update(String(password || ""))
    .digest("hex");
}

function createPlayerId() {
  return crypto.randomUUID ? crypto.randomUUID() : crypto.randomBytes(16).toString("hex");
}

function normalizeLetter(letter) {
  const value = String(letter || "").trim().toUpperCase();
  return value === "O" ? "O" : value === "S" ? "S" : "";
}

function normalizeSettings(settings = {}) {
  const rows = clamp(Number(settings.rows || settings.size) || 5, MIN_BOARD_SIDE, MAX_BOARD_SIDE);
  const cols = clamp(Number(settings.cols || settings.size) || 5, MIN_BOARD_SIDE, MAX_BOARD_SIDE);
  const theme = THEMES.has(settings.theme) ? settings.theme : "classic";
  const totalPlayers = clamp(Number(settings.totalPlayers) || 2, MIN_TOTAL_PLAYERS, MAX_TOTAL_PLAYERS);
  const botCount = clamp(Number(settings.botCount) || 0, 0, totalPlayers - 1);
  const moveTimeSeconds = clamp(
    Number(settings.moveTimeSeconds) || DEFAULT_MOVE_TIME_SECONDS,
    MIN_MOVE_TIME_SECONDS,
    MAX_MOVE_TIME_SECONDS
  );
  const useMoveTimer = ![false, "false", 0, "0", "off"].includes(settings.useMoveTimer);

  return { rows, cols, theme, totalPlayers, botCount, useMoveTimer, moveTimeSeconds };
}

function getRequiredHumanCount(settings) {
  return Math.max(1, settings.totalPlayers - settings.botCount);
}

function createRoomCode() {
  const alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let code = "";

  do {
    code = Array.from({ length: ROOM_CODE_LENGTH }, () => {
      const index = Math.floor(Math.random() * alphabet.length);
      return alphabet[index];
    }).join("");
  } while (rooms.has(code));

  return code;
}

function createBotPlayer(roomCode, number) {
  return {
    id: `BOT-${roomCode}-${number}`,
    name: number === 1 ? BOT_BASE_NAME : `${BOT_BASE_NAME} ${number}`,
    isBot: true
  };
}

function isBotPlayer(player) {
  return Boolean(player && player.isBot);
}

function getHumanPlayers(room) {
  return room.players.filter(player => !isBotPlayer(player));
}

function syncRoomBots(room) {
  const humans = getHumanPlayers(room);
  const maxBotsAllowed = Math.max(0, room.settings.totalPlayers - humans.length);
  room.settings.botCount = Math.min(room.settings.botCount, maxBotsAllowed);
  room.players = humans.concat(
    Array.from({ length: room.settings.botCount }, (_unused, index) => createBotPlayer(room.code, index + 1))
  );
}

function createBoard(rows, cols) {
  return Array.from({ length: rows }, () => Array(cols).fill(""));
}

function cloneBoard(board) {
  return board.map(row => row.slice());
}

function inBounds(rows, cols, row, col) {
  return row >= 0 && row < rows && col >= 0 && col < cols;
}

function sequenceKey(cells) {
  return cells.map(cell => `${cell.r},${cell.c}`).join("|");
}

function findSosSequences(board, rows, cols, row, col) {
  const found = [];

  for (const [dr, dc] of DIRECTIONS) {
    for (let offset = -2; offset <= 0; offset++) {
      const cells = [0, 1, 2].map(step => ({
        r: row + (offset + step) * dr,
        c: col + (offset + step) * dc
      }));

      if (!cells.every(cell => inBounds(rows, cols, cell.r, cell.c))) continue;

      const word = cells.map(cell => board[cell.r][cell.c]).join("");
      if (word === "SOS") {
        found.push({
          key: sequenceKey(cells),
          cells
        });
      }
    }
  }

  return found;
}

function getAvailableMoves(gameState) {
  const moves = [];

  for (let row = 0; row < gameState.rows; row++) {
    for (let col = 0; col < gameState.cols; col++) {
      if (!gameState.board[row][col]) {
        moves.push({ row, col, letter: "S" });
        moves.push({ row, col, letter: "O" });
      }
    }
  }

  return moves;
}

function countNewSequencesForMove(gameState, move) {
  if (gameState.board[move.row][move.col]) return 0;

  const board = cloneBoard(gameState.board);
  board[move.row][move.col] = move.letter;
  const existing = new Set(gameState.sequences.map(sequence => sequence.key));

  return findSosSequences(board, gameState.rows, gameState.cols, move.row, move.col)
    .filter(sequence => !existing.has(sequence.key))
    .length;
}

function wouldOpponentScoreAfterMove(gameState, move) {
  if (gameState.board[move.row][move.col]) return 0;

  const board = cloneBoard(gameState.board);
  board[move.row][move.col] = move.letter;
  const trialState = {
    ...gameState,
    board
  };

  let best = 0;
  for (const nextMove of getAvailableMoves(trialState)) {
    best = Math.max(best, countNewSequencesForMove(trialState, nextMove));
  }

  return best;
}

function chooseBotMove(room) {
  const gameState = room.gameState;
  if (!gameState) return null;

  const moves = getAvailableMoves(gameState);
  if (!moves.length) return null;

  const centerRow = (gameState.rows - 1) / 2;
  const centerCol = (gameState.cols - 1) / 2;
  const scored = moves
    .map(move => ({
      move,
      gained: countNewSequencesForMove(gameState, move),
      risk: wouldOpponentScoreAfterMove(gameState, move),
      distance: Math.abs(move.row - centerRow) + Math.abs(move.col - centerCol)
    }))
    .sort((left, right) => {
      if (right.gained !== left.gained) return right.gained - left.gained;
      if (left.risk !== right.risk) return left.risk - right.risk;
      return left.distance - right.distance;
    });

  const goodMoves = scored.filter(entry => entry.gained > 0 || entry.risk === 0);
  const pool = goodMoves.length ? goodMoves : scored;
  return pool[0].move;
}

function chooseRandomMove(room) {
  if (!room.gameState) return null;

  const moves = getAvailableMoves(room.gameState);
  if (!moves.length) return null;

  return moves[Math.floor(Math.random() * moves.length)];
}

function serializeRoom(room, notice = room.notice || "") {
  return {
    roomCode: room.code,
    hostId: room.hostId,
    players: room.players.map(player => ({ ...player })),
    settings: { ...room.settings },
    started: room.started,
    notice
  };
}

function serializeGameState(room) {
  if (!room.gameState) return null;

  return {
    rows: room.gameState.rows,
    cols: room.gameState.cols,
    theme: room.gameState.theme,
    players: room.players.map(player => ({ ...player })),
    scores: room.gameState.scores.slice(),
    currentPlayer: room.gameState.currentPlayer,
    board: cloneBoard(room.gameState.board),
    sequences: room.gameState.sequences.map(sequence => ({
      key: sequence.key,
      cells: sequence.cells.map(cell => ({ ...cell })),
      ownerIndex: sequence.ownerIndex,
      falseScore: Boolean(sequence.falseScore)
    })),
    lastMove: room.gameState.lastMove
      ? {
          ...room.gameState.lastMove,
          completedSequences: room.gameState.lastMove.completedSequences.map(sequence => sequence.key)
        }
      : null,
    finished: room.gameState.finished,
    useMoveTimer: room.settings.useMoveTimer !== false,
    moveTimeSeconds: room.settings.moveTimeSeconds,
    turnStartedAt: room.gameState.turnStartedAt,
    turnDeadlineAt: room.gameState.turnDeadlineAt
  };
}

function markRoom(room, notice = "") {
  room.notice = notice;
  room.updatedAt = Date.now();
}

function createInitialGameState(room) {
  return {
    rows: room.settings.rows,
    cols: room.settings.cols,
    theme: room.settings.theme,
    scores: new Array(room.players.length).fill(0),
    currentPlayer: 0,
    turnStartedAt: null,
    turnDeadlineAt: null,
    board: createBoard(room.settings.rows, room.settings.cols),
    sequences: [],
    lastMove: null,
    finished: false
  };
}

function normalizeMove(rawMove = {}) {
  const row = Number(rawMove.row);
  const col = Number(rawMove.col);
  const letter = normalizeLetter(rawMove.letter);

  if (!Number.isInteger(row) || !Number.isInteger(col) || !letter) {
    return null;
  }

  return { row, col, letter };
}

function applyMove(room, playerId, rawMove, options = {}) {
  if (!room.gameState) {
    return { ok: false, error: "The match has not started yet." };
  }

  const move = normalizeMove(rawMove);
  if (!move || !inBounds(room.gameState.rows, room.gameState.cols, move.row, move.col)) {
    return { ok: false, error: "That move is not valid on this board." };
  }

  const playerIndex = room.players.findIndex(player => player.id === playerId);
  if (playerIndex === -1) {
    return { ok: false, error: "You are not part of this room." };
  }

  if (playerIndex !== room.gameState.currentPlayer) {
    return { ok: false, error: "It is not your turn yet." };
  }

  if (room.gameState.board[move.row][move.col]) {
    return { ok: false, error: "That square is already taken." };
  }

  room.gameState.board[move.row][move.col] = move.letter;

  const existingSequences = new Set(room.gameState.sequences.map(sequence => sequence.key));
  const falseScore = Boolean(options.falseScore);
  const completedSequences = findSosSequences(
    room.gameState.board,
    room.gameState.rows,
    room.gameState.cols,
    move.row,
    move.col
  ).filter(sequence => !existingSequences.has(sequence.key));

  completedSequences.forEach(sequence => {
    room.gameState.sequences.push({
      ...sequence,
      ownerIndex: falseScore ? -1 : playerIndex,
      falseScore
    });
  });

  if (!falseScore && completedSequences.length) {
    room.gameState.scores[playerIndex] += completedSequences.length;
  }

  if (!completedSequences.length || options.forceAdvanceTurn || falseScore) {
    room.gameState.currentPlayer = (room.gameState.currentPlayer + 1) % room.players.length;
  }

  room.gameState.lastMove = {
    row: move.row,
    col: move.col,
    letter: move.letter,
    ownerIndex: playerIndex,
    completedSequences,
    timeout: Boolean(options.timeout),
    falseScore
  };

  const occupied = room.gameState.board.reduce(
    (count, row) => count + row.filter(Boolean).length,
    0
  );
  if (occupied === room.gameState.rows * room.gameState.cols) {
    room.gameState.finished = true;
    room.gameState.turnDeadlineAt = null;
    room.started = false;
    clearRoomTimers(room);
  }

  markRoom(room);
  return { ok: true };
}

function clearBotTurnTimer(room) {
  if (room.botTurnTimer) {
    clearTimeout(room.botTurnTimer);
    room.botTurnTimer = null;
  }
}

function clearTurnTimer(room) {
  if (room.turnTimer) {
    clearTimeout(room.turnTimer);
    room.turnTimer = null;
  }
}

function clearRoomTimers(room) {
  clearBotTurnTimer(room);
  clearTurnTimer(room);
}

function scheduleTurnTimer(room) {
  clearTurnTimer(room);

  if (!room.started || !room.gameState || room.gameState.finished) {
    return;
  }

  const currentPlayer = room.players[room.gameState.currentPlayer];
  const now = Date.now();
  room.gameState.turnStartedAt = now;

  if (!currentPlayer || isBotPlayer(currentPlayer) || room.settings.useMoveTimer === false) {
    room.gameState.turnDeadlineAt = null;
    markRoom(room);
    return;
  }

  const moveTimeMs = (room.settings.moveTimeSeconds || DEFAULT_MOVE_TIME_SECONDS) * 1000;
  room.gameState.turnDeadlineAt = now + moveTimeMs;
  room.turnTimer = setTimeout(() => {
    room.turnTimer = null;
    runTurnTimeout(room);
  }, moveTimeMs);
  markRoom(room);
}

function finishRoomIfNoMoves(room) {
  if (!room.gameState || getAvailableMoves(room.gameState).length) {
    return false;
  }

  room.gameState.finished = true;
  room.started = false;
  clearRoomTimers(room);
  markRoom(room, "Match finished. Host can start a rematch.");
  return true;
}

function runTurnTimeout(room) {
  if (!room.started || !room.gameState || room.gameState.finished) {
    return;
  }

  const currentPlayer = room.players[room.gameState.currentPlayer];
  if (!currentPlayer || isBotPlayer(currentPlayer)) {
    scheduleBotTurn(room);
    return;
  }

  const move = chooseRandomMove(room);
  if (!move) {
    finishRoomIfNoMoves(room);
    return;
  }

  const result = applyMove(room, currentPlayer.id, move, {
    timeout: true,
    falseScore: true,
    forceAdvanceTurn: true
  });

  if (!result.ok) {
    console.error("Timeout move failed:", result.error);
    return;
  }

  if (room.gameState.finished) {
    markRoom(room, "Match finished. Host can start a rematch.");
    return;
  }

  scheduleTurnTimer(room);
  scheduleBotTurn(room);
}

function runBotTurn(room) {
  clearBotTurnTimer(room);

  if (!room.started || !room.gameState || room.gameState.finished) {
    return;
  }

  const currentPlayer = room.players[room.gameState.currentPlayer];
  if (!isBotPlayer(currentPlayer)) {
    return;
  }

  const move = chooseBotMove(room);
  if (!move) {
    finishRoomIfNoMoves(room);
    return;
  }

  const result = applyMove(room, currentPlayer.id, move);
  if (!result.ok) {
    console.error("Bot move failed:", result.error);
    return;
  }

  scheduleTurnTimer(room);

  if (room.gameState.finished) {
    markRoom(room, "Match finished. Host can start a rematch.");
    return;
  }

  scheduleBotTurn(room);
}

function scheduleBotTurn(room) {
  clearBotTurnTimer(room);

  if (!room.started || !room.gameState || room.gameState.finished) {
    return;
  }

  const currentPlayer = room.players[room.gameState.currentPlayer];
  if (!isBotPlayer(currentPlayer)) {
    return;
  }

  room.botTurnTimer = setTimeout(() => {
    room.botTurnTimer = null;
    runBotTurn(room);
  }, BOT_THINK_TIME_MS);
}

function leaveRoomByPlayerId(playerId, reason = "left the room") {
  for (const room of rooms.values()) {
    const index = room.players.findIndex(player => player.id === playerId);
    if (index === -1) continue;

    clearRoomTimers(room);
    const [player] = room.players.splice(index, 1);
    const remainingHumans = getHumanPlayers(room);

    if (!remainingHumans.length) {
      rooms.delete(room.code);
      return;
    }

    if (room.hostId === playerId) {
      room.hostId = remainingHumans[0].id;
    }

    room.started = false;
    room.gameState = null;
    syncRoomBots(room);
    markRoom(room, `${player.name} ${reason}.`);
    return;
  }
}

function getRoomFromPayload(payload = {}) {
  const code = normalizeRoomCode(payload.roomCode);
  return rooms.get(code) || null;
}

function createRoom(payload) {
  const playerName = normalizePlayerName(payload.playerName);
  const password = String(payload.password || "");

  if (!password.trim()) {
    return { ok: false, error: "Room password is required." };
  }

  const playerId = createPlayerId();
  const code = createRoomCode();
  const settings = normalizeSettings(payload.settings);
  const room = {
    code,
    hostId: playerId,
    passwordHash: hashPassword(password),
    players: [
      {
        id: playerId,
        name: playerName
      }
    ],
    settings,
    started: false,
    gameState: null,
    turnTimer: null,
    botTurnTimer: null,
    notice: "",
    updatedAt: Date.now()
  };

  syncRoomBots(room);
  rooms.set(code, room);
  markRoom(room, `Room ${code} created.`);

  return {
    ok: true,
    roomCode: code,
    playerId,
    room: serializeRoom(room)
  };
}

function joinRoom(payload) {
  const code = normalizeRoomCode(payload.roomCode);
  const room = rooms.get(code);
  const playerName = normalizePlayerName(payload.playerName);

  if (!room) {
    return { ok: false, error: "Room not found." };
  }

  if (room.passwordHash !== hashPassword(payload.password || "")) {
    return { ok: false, error: "Wrong room password." };
  }

  if (room.started) {
    return { ok: false, error: "That match already started." };
  }

  const humanPlayers = getHumanPlayers(room);
  if (humanPlayers.length >= getRequiredHumanCount(room.settings)) {
    return { ok: false, error: "Room is full." };
  }

  const playerId = createPlayerId();
  room.players = room.players.filter(player => !isBotPlayer(player));
  room.players.push({
    id: playerId,
    name: playerName
  });
  syncRoomBots(room);
  markRoom(room, `${playerName} joined the room.`);

  return {
    ok: true,
    roomCode: room.code,
    playerId,
    room: serializeRoom(room)
  };
}

function updateRoomSettings(payload) {
  const room = getRoomFromPayload(payload);
  if (!room) return { ok: false, error: "Join a room first." };
  if (room.hostId !== payload.playerId) return { ok: false, error: "Only the host can change room settings." };
  if (room.started) return { ok: false, error: "You cannot change settings during a live match." };

  room.settings = {
    ...room.settings,
    ...normalizeSettings(payload.settings || payload)
  };
  syncRoomBots(room);
  markRoom(room, "Room settings updated.");
  return { ok: true, room: serializeRoom(room) };
}

function startOnlineGame(payload) {
  const room = getRoomFromPayload(payload);
  if (!room) return { ok: false, error: "Join a room first." };
  if (room.hostId !== payload.playerId) return { ok: false, error: "Only the host can start the match." };

  const requiredHumans = getRequiredHumanCount(room.settings);
  if (getHumanPlayers(room).length < requiredHumans) {
    return { ok: false, error: `Need ${requiredHumans} human player(s) before starting.` };
  }

  syncRoomBots(room);
  room.started = true;
  room.gameState = createInitialGameState(room);
  markRoom(room, "Match started.");
  scheduleTurnTimer(room);
  scheduleBotTurn(room);
  return { ok: true, room: serializeRoom(room), game: serializeGameState(room) };
}

function playMove(payload) {
  const room = getRoomFromPayload(payload);
  if (!room) return { ok: false, error: "Join a room first." };

  const result = applyMove(room, payload.playerId, payload);
  if (!result.ok) return result;

  clearTurnTimer(room);
  scheduleTurnTimer(room);

  if (room.gameState && room.gameState.finished) {
    markRoom(room, "Match finished. Host can start a rematch.");
  } else {
    scheduleBotTurn(room);
  }

  return { ok: true, game: serializeGameState(room) };
}

function getRoomState(payload) {
  const room = getRoomFromPayload(payload);
  if (!room) return { ok: false, error: "Room not found." };
  return { ok: true, room: serializeRoom(room) };
}

function getGameState(payload) {
  const room = getRoomFromPayload(payload);
  if (!room) return { ok: false, error: "Room not found." };
  return { ok: true, game: serializeGameState(room) };
}

function leaveRoom(payload) {
  leaveRoomByPlayerId(payload.playerId, "left the room");
  return { ok: true };
}

function sendJson(res, status, payload) {
  const body = JSON.stringify(payload);
  res.writeHead(status, {
    "Content-Type": "application/json; charset=utf-8",
    "Cache-Control": "no-store",
    "X-Content-Type-Options": "nosniff",
    "Content-Length": Buffer.byteLength(body)
  });
  res.end(body);
}

function readJson(req) {
  return new Promise((resolve, reject) => {
    let body = "";
    req.on("data", chunk => {
      body += chunk;
      if (body.length > 1024 * 1024) {
        req.destroy();
        reject(new Error("Request body is too large."));
      }
    });
    req.on("end", () => {
      if (!body) {
        resolve({});
        return;
      }
      try {
        resolve(JSON.parse(body));
      } catch {
        reject(new Error("Invalid JSON."));
      }
    });
    req.on("error", reject);
  });
}

function contentTypeFor(filePath) {
  const ext = path.extname(filePath).toLowerCase();
  if (ext === ".html") return "text/html; charset=utf-8";
  if (ext === ".js") return "text/javascript; charset=utf-8";
  if (ext === ".css") return "text/css; charset=utf-8";
  if (ext === ".json") return "application/json; charset=utf-8";
  if (ext === ".webmanifest") return "application/manifest+json; charset=utf-8";
  if (ext === ".png") return "image/png";
  if (ext === ".jpg" || ext === ".jpeg") return "image/jpeg";
  if (ext === ".svg") return "image/svg+xml";
  return "application/octet-stream";
}

function setCorsHeaders(req, res) {
  const origin = req.headers.origin || "*";
  res.setHeader("Access-Control-Allow-Origin", origin);
  res.setHeader("Access-Control-Allow-Methods", "GET,POST,HEAD,OPTIONS");
  res.setHeader("Access-Control-Allow-Headers", "Content-Type");
  res.setHeader("Vary", "Origin");
}

function isPathInside(baseDir, targetPath) {
  const relative = path.relative(baseDir, targetPath);
  return relative === "" || (!!relative && !relative.startsWith("..") && !path.isAbsolute(relative));
}

function serveStatic(req, res, parsedUrl) {
  const pathname = decodeURIComponent(parsedUrl.pathname);
  const relative = pathname === "/" ? "index.html" : pathname.replace(/^\/+/, "");
  const safePath = path.normalize(relative).replace(/^(\.\.[/\\])+/, "");
  let filePath = path.resolve(PUBLIC_DIR, safePath);

  if (!isPathInside(PUBLIC_DIR, filePath)) {
    sendJson(res, 403, { ok: false, error: "Forbidden." });
    return;
  }

  if (!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) {
    filePath = path.join(PUBLIC_DIR, "index.html");
  }

  fs.readFile(filePath, (error, data) => {
    if (error) {
      sendJson(res, 404, { ok: false, error: "Not found." });
      return;
    }
    const fileName = path.basename(filePath);
    const headers = {
      "Content-Type": contentTypeFor(filePath),
      "Cache-Control": fileName === "index.html" || fileName === "sw.js" ? "no-cache" : "public, max-age=86400",
      "X-Content-Type-Options": "nosniff"
    };

    if (fileName === "sw.js") {
      headers["Service-Worker-Allowed"] = "/";
    }

    res.writeHead(200, headers);
    res.end(req.method === "HEAD" ? undefined : data);
  });
}

async function handleApi(req, res, parsedUrl) {
  const queryPayload = Object.fromEntries(parsedUrl.searchParams.entries());
  let payload = queryPayload;

  if (req.method !== "GET") {
    try {
      payload = await readJson(req);
    } catch (error) {
      sendJson(res, 400, { ok: false, error: error.message });
      return;
    }
  }

  const route = `${req.method} ${parsedUrl.pathname}`;
  const handlers = {
    "GET /health": () => ({ ok: true, rooms: rooms.size }),
    "POST /api/create-room": createRoom,
    "POST /api/join-room": joinRoom,
    "POST /api/update-room-settings": updateRoomSettings,
    "POST /api/start-online-game": startOnlineGame,
    "POST /api/play-move": playMove,
    "POST /api/leave-room": leaveRoom,
    "GET /api/room-state": getRoomState,
    "GET /api/game-state": getGameState
  };

  const handler = handlers[route];
  if (!handler) {
    sendJson(res, 404, { ok: false, error: "API route not found." });
    return;
  }

  try {
    const result = handler(payload);
    sendJson(res, result.ok === false ? 400 : 200, result);
  } catch (error) {
    console.error(error);
    sendJson(res, 500, { ok: false, error: "Server error." });
  }
}

const server = http.createServer((req, res) => {
  setCorsHeaders(req, res);

  if (req.method === "OPTIONS") {
    res.writeHead(204);
    res.end();
    return;
  }

  const parsedUrl = new URL(req.url, `http://${req.headers.host || "localhost"}`);

  if (parsedUrl.pathname === "/health" || parsedUrl.pathname.startsWith("/api/")) {
    handleApi(req, res, parsedUrl);
    return;
  }

  if (req.method !== "GET" && req.method !== "HEAD") {
    sendJson(res, 405, { ok: false, error: "Method not allowed." });
    return;
  }

  serveStatic(req, res, parsedUrl);
});

const PORT = Number(process.env.PORT) || 3000;
const HOST = process.env.HOST || "0.0.0.0";

server.listen(PORT, HOST, () => {
  console.log(`Thankans SOS server running on http://${HOST}:${PORT}`);
});

function shutdown(signal) {
  console.log(`${signal} received. Closing Thankans SOS server.`);
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 5000).unref();
}

process.on("SIGTERM", () => shutdown("SIGTERM"));
process.on("SIGINT", () => shutdown("SIGINT"));
