const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const { randomInt } = require('crypto');
const WORD_SETS = require('./words');
const TABOO_WORDS = require('./taboo-words');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static('public', {
  maxAge: '1h',
  etag: true,
  lastModified: true,
  setHeaders(res, filePath) {
    if (/[/\\]index\.html$/i.test(filePath)) res.setHeader('Cache-Control', 'no-cache');
  },
}));

const SUITS = ['♠', '♥', '♦', '♣'];
const RANKS = ['A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];
const SURVIVE_CARDS = 16;          // จำนวนไพ่เกมรอดหรือร่วง
const LEAVE_GRACE_MS = 60000;      // คนหลุดจะถูกลบออกจากห้องอัตโนมัติหลัง 60 วิ
const TIMER_MIN = 1, TIMER_MAX = 15; // เกมหยุดเวลา: สุ่ม 1-15 วิ
const TIMER_COUNTDOWN_MS = 2850;   // ช่วง 3-2-1 + ตี้ดยาว
const TIMER_EXTRA_MS = 10000;      // เลยเป้าหมายไปแล้ว 10 วิ ยังไม่กด = แพ้
const GAMES = ['lobby', 'cards', 'survive', 'dice', 'word', 'taboo', 'timer'];
const rooms = {};
let roundSeq = 0;

function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function newDeck() {
  const d = [];
  for (const s of SUITS) for (const r of RANKS) d.push({ s, r });
  return shuffle(d); // 52 ใบ ไม่มีโจ๊กเกอร์
}

const nameOf = (room, pid) => room.players[pid]?.name || '?';
const activeIds = room => Object.keys(room.players).filter(id => room.players[id].sid);

// ---------- ระบบคิว (รอดหรือร่วง + ลูกเต๋า) ----------
function nextTurn(room, fromId) {
  const all = Object.keys(room.players);
  const n = all.length;
  if (n === 0) return null;
  const idx = all.indexOf(fromId);
  for (let k = 1; k <= n; k++) {
    const id = all[(idx + k) % n];
    if (room.players[id]?.sid) return id;
  }
  return null;
}

function ensureTurn(room) {
  const s = room.state;
  if (room.game === 'survive' && s.loser) return;
  if (room.game === 'survive' || room.game === 'dice') {
    if (!s.turn || !room.players[s.turn]?.sid) s.turn = nextTurn(room, s.turn);
  }
}

// ---------- รอดหรือร่วง ----------
function newSurviveRound(room, afterId = null) {
  room.secret.bad = randomInt(SURVIVE_CARDS);
  room.state = {
    total: SURVIVE_CARDS,
    opened: [],
    loser: null,
    turn: nextTurn(room, afterId),
    roundId: ++roundSeq,
  };
}

// ---------- คำเดียวกัน ----------
function newWordRound(room) {
  let set;
  do { set = WORD_SETS[randomInt(WORD_SETS.length)]; }
  while (set.cat === room.lastCat && WORD_SETS.length > 1);
  room.lastCat = set.cat;
  room.secret.picks = {};
  room.state = { set: { cat: set.cat, words: shuffle([...set.words]) }, pickedIds: [], result: null };
}

// ---------- คำต้องห้าม ----------
function newTabooRound(room) {
  const ids = activeIds(room);
  room.tabooLastWords ||= {};
  const recentlyUsed = new Set(Object.values(room.tabooLastWords));
  const words = shuffle([...new Set(TABOO_WORDS)].filter(word => !recentlyUsed.has(word)));
  if (words.length < ids.length) return false;
  room.secret.tabooWords = Object.fromEntries(ids.map((id, i) => [id, words[i]]));
  Object.assign(room.tabooLastWords, room.secret.tabooWords);
  room.state = { roundId: ++roundSeq, participants: ids, status: 'playing', mode: 'random', losers: [], winner: null };
  return true;
}

function startCustomTabooIfReady(room) {
  const s = room.state;
  const entries = room.secret.tabooCustomWords || {};
  const ids = s.participants.filter(id => !!room.players[id]);
  s.participants = ids;
  if (!ids.length || !ids.every(id => entries[id])) return false;
  room.secret.tabooWords = Object.fromEntries(ids.map(id => [id, entries[id]]));
  Object.assign(room.tabooLastWords ||= {}, room.secret.tabooWords);
  s.roundId = ++roundSeq;
  s.status = 'playing';
  s.losers = [];
  s.winner = null;
  return true;
}

function checkWord(room) {
  if (room.game !== 'word' || room.state.result) return;
  const ids = activeIds(room);
  const picks = room.secret.picks;
  if (ids.length < 2 || !ids.every(id => id in picks)) return;

  const groups = {};
  for (const id of ids) (groups[picks[id]] ??= []).push(nameOf(room, id));
  const counts = Object.values(groups).map(g => g.length);
  const min = Math.min(...counts), max = Math.max(...counts);

  let result;
  if (min === max) {
    result = { type: counts.length === 1 ? 'allSame' : 'tie' };
  } else {
    const losers = Object.values(groups).filter(g => g.length === min).flat();
    result = { type: 'lose', losers };
  }
  result.reveal = ids.map(id => ({ name: nameOf(room, id), word: room.state.set.words[picks[id]] }));
  room.state.result = result;

  if (result.type !== 'lose') {
    setTimeout(() => {
      if (rooms[room.code] === room && room.game === 'word' && room.state.result === result) {
        newWordRound(room);
        broadcast(room);
      }
    }, 3000);
  }
}

// ---------- หยุดเวลา ----------
function timerIdle() {
  return { phase: 'idle', target: null, roundId: ++roundSeq, participants: [], pressedIds: [], outcome: null, startedBy: null };
}

function startTimerRound(room, by) {
  clearTimeout(room.secret.timeout);
  const target = randomInt(TIMER_MIN, TIMER_MAX + 1);
  room.secret = { times: {}, startedAt: Date.now() };
  room.state = {
    phase: 'running',
    target,
    roundId: ++roundSeq,
    participants: activeIds(room), // คนที่ออนไลน์ตอนกดเริ่ม = คนเล่นรอบนี้
    pressedIds: [],
    outcome: null,
    startedBy: by,
  };
  const r = room, rid = room.state.roundId;
  room.secret.timeout = setTimeout(() => {
    if (rooms[r.code] === r && r.game === 'timer' && r.state.roundId === rid) {
      finishTimer(r);
      broadcast(r);
    }
  }, TIMER_COUNTDOWN_MS + target * 1000 + TIMER_EXTRA_MS);
}

function finishTimer(room) {
  const s = room.state;
  if (room.game !== 'timer' || s.phase !== 'running') return;
  clearTimeout(room.secret.timeout);
  const goal = s.target * 1000;
  const rows = s.participants.filter(id => room.players[id]).map(id => {
    const ms = room.secret.times[id];
    return { name: nameOf(room, id), ms: ms ?? null, diff: ms == null ? null : Math.abs(ms - goal) };
  });
  const d = r => (r.diff == null ? Infinity : r.diff);
  rows.sort((a, b) => (d(a) === d(b) ? 0 : d(a) - d(b))); // ใกล้สุดอยู่บน
  const worst = rows.length ? d(rows[rows.length - 1]) : null;
  const losers = rows.length > 0 ? rows.filter(r => d(r) === worst).map(r => r.name) : [];
  s.phase = 'result';
  s.outcome = { rows, losers };
}

function checkTimer(room) {
  const s = room.state;
  if (room.game !== 'timer' || s.phase !== 'running') return;
  const times = room.secret.times;
  // คนที่หลุดและยังไม่ได้กด = ตัดออกจากรอบ
  s.participants = s.participants.filter(id => (id in times ? !!room.players[id] : !!room.players[id]?.sid));
  s.pressedIds = s.participants.filter(id => id in times);
  if (s.participants.every(id => id in times)) finishTimer(room);
}

// ---------- ทั่วไป ----------
function initGame(room, game) {
  clearTimeout(room.secret?.timeout);
  clearTimeout(room.punishmentRoll?.timeout);
  room.punishmentRoll = null;
  room.game = game;
  room.secret = {};
  if (game === 'lobby') room.state = {};
  if (game === 'cards') {
    room.secret.deck = newDeck();
    room.state = { current: null, remaining: 52, flippedBy: null, history: [] };
  }
  if (game === 'survive') newSurviveRound(room);
  if (game === 'dice') room.state = { value: null, by: null, rollId: 0, turn: nextTurn(room, null) };
  if (game === 'word') newWordRound(room);
  if (game === 'taboo') {
    room.state = { roundId: null, participants: activeIds(room), status: 'mode', mode: null, losers: [], winner: null };
  }
  if (game === 'timer') room.state = timerIdle();
}

function publicRoom(r, playerId) {
  const lossKey = currentPunishmentKey(r);
  const roll = lossKey && r.punishmentRoll?.key === lossKey ? r.punishmentRoll : null;
  return {
    code: r.code,
    game: r.game,
    musicElapsedMs: Math.max(0, Date.now() - (r.musicStartedAt || Date.now())),
    state: r.game === 'taboo' ? {
      roundId: r.state.roundId,
      status: r.state.status,
      mode: r.state.mode,
      losers: (r.state.losers || []).map(({ id, name }) => ({ id, name })),
      winner: r.state.winner ? { id: r.state.winner.id, name: r.state.winner.name } : null,
      isParticipant: !!r.state.participants?.includes(playerId),
      myWord: r.state.status === 'playing' ? r.secret.tabooWords?.[playerId] || null : null,
      submittedCount: r.state.status === 'setup' ? Object.keys(r.secret.tabooCustomWords || {}).filter(id => r.state.participants?.includes(id)).length : 0,
      participantCount: r.state.participants?.length || 0,
      hasSubmitted: !!r.secret.tabooCustomWords?.[playerId],
    } : r.state,
    punishmentRoll: roll ? {
      key: roll.key,
      status: roll.status,
      outcome: roll.status === 'result' ? roll.outcome : null,
      rotation: roll.rotation,
    } : null,
    players: Object.entries(r.players).map(([id, p]) => ({ id, name: p.name, online: !!p.sid })),
  };
}

function currentPunishmentKey(room) {
  const s = room.state;
  if (room.game === 'survive' && s.loser) return `survive:${s.roundId}`;
  if (room.game === 'word' && s.result?.type === 'lose') {
    return `word:${s.set.cat}:${s.result.reveal.map(x => `${x.name}=${x.word}`).join('|')}`;
  }
  if (room.game === 'timer' && s.phase === 'result' && s.outcome?.losers?.length) return `timer:${s.roundId}`;
  return null;
}

function punishedPlayerIds(room) {
  const s = room.state;
  if (room.game === 'survive' && s.loser?.id) return [s.loser.id];
  if (room.game === 'word' && s.result?.type === 'lose') {
    return s.result.losers.map(name => Object.keys(room.players).find(id => room.players[id].name === name)).filter(Boolean);
  }
  if (room.game === 'timer' && s.phase === 'result' && s.outcome?.losers?.length) {
    return s.outcome.losers.map(name => Object.keys(room.players).find(id => room.players[id].name === name)).filter(Boolean);
  }
  return [];
}

function neighborId(room, direction) {
  const order = Object.keys(room.players);
  if (order.length < 2) return null;
  const base = order.indexOf(punishedPlayerIds(room)[0]);
  if (base < 0) return null;
  return order[(base + direction + order.length) % order.length];
}

function broadcast(room) {
  for (const [id, player] of Object.entries(room.players)) {
    if (player.sid) io.to(player.sid).emit('room', publicRoom(room, id));
  }
}

// เช็กสถานะเกมใหม่ทุกครั้งที่มีคนเข้า/ออก/หลุด
function refresh(room) {
  ensureTurn(room);
  if (room.game === 'word' && room.secret.picks) {
    for (const id of Object.keys(room.secret.picks)) {
      if (!room.players[id]) delete room.secret.picks[id];
    }
    room.state.pickedIds = Object.keys(room.secret.picks);
    checkWord(room);
  }
  if (room.game === 'timer') checkTimer(room);
  if (room.game === 'taboo' && room.state.status === 'setup') startCustomTabooIfReady(room);
}

function removePlayer(room, pid) {
  const p = room.players[pid];
  if (!p) return;
  clearTimeout(p.timer);
  p.sid = null;
  if (room.state.turn === pid) room.state.turn = nextTurn(room, pid);
  delete room.players[pid];
  if (Object.keys(room.players).length === 0) {
    clearTimeout(room.secret?.timeout);
    delete rooms[room.code];
    return;
  }
  refresh(room);
  broadcast(room);
}

io.on('connection', socket => {
  let room = null, pid = null;
  const ok = game => room && (!game || room.game === game) && room.players[pid]?.sid === socket.id;

  socket.on('join', data => {
    if (room) return;
    const code = String(data?.code || '').toUpperCase().trim().slice(0, 6);
    const name = String(data?.name || '').trim().slice(0, 20);
    let id = String(data?.pid || '').trim().slice(0, 40) || socket.id;
    if (!code || !name) return socket.emit('err', 'กรอกชื่อกับรหัสห้องด้วย');

    if (!rooms[code]) rooms[code] = { code, players: {}, game: 'lobby', state: {}, secret: {}, musicStartedAt: Date.now() };
    room = rooms[code];
    if (!room.musicStartedAt) room.musicStartedAt = Date.now();

    // ชื่อเดียวกันที่หลุดค้างอยู่ = คนเดิมกลับมา
    if (!room.players[id]) {
      const ghost = Object.keys(room.players).find(k => !room.players[k].sid && room.players[k].name === name);
      if (ghost) id = ghost;
    }
    pid = id;

    const old = room.players[pid];
    if (old) {
      clearTimeout(old.timer);
      old.timer = null;
      const prevSid = old.sid;
      old.sid = socket.id;
      old.name = name;
      if (prevSid && prevSid !== socket.id) {
        const prev = io.sockets.sockets.get(prevSid);
        prev?.emit('err', 'บัญชีนี้เข้าจากแท็บอื่นแล้ว');
        prev?.disconnect(true);
      }
    } else {
      room.players[pid] = { name, sid: socket.id, timer: null };
    }
    socket.join(code);
    socket.emit('you', pid);
    refresh(room);
    broadcast(room);
  });

  socket.on('leave', () => {
    if (!ok()) return;
    const r = room, id = pid;
    socket.leave(r.code);
    room = null; pid = null;
    removePlayer(r, id);
  });

  // เคลียร์คนหลุดทั้งหมดในครั้งเดียว
  socket.on('kickOffline', () => {
    if (!ok()) return;
    for (const [id, p] of Object.entries(room.players)) {
      if (p.sid) continue;
      if (room.state.turn === id) room.state.turn = nextTurn(room, id);
      clearTimeout(p.timer);
      delete room.players[id];
    }
    refresh(room);
    broadcast(room);
  });

  socket.on('selectGame', g => {
    if (!ok() || !GAMES.includes(g)) return;
    initGame(room, g);
    broadcast(room);
  });

  socket.on('punishment:spin', key => {
    if (!ok() || typeof key !== 'string' || key !== currentPunishmentKey(room)) return;
    const eligibleIds = punishedPlayerIds(room);
    if (!eligibleIds.includes(pid)) {
      const eligibleNames = eligibleIds.map(id => room.players[id]?.name).filter(Boolean);
      socket.emit('err', 'กดเสี่ยงดวงได้เฉพาะ ' + eligibleNames.join(' และ ') + ' เท่านั้น');
      return;
    }
    if (room.punishmentRoll?.key === key) return;
    const outcome = randomInt(6);
    const roll = {
      key, status: 'spinning', outcome, targetId: null,
      rotation: 1800 + randomInt(5) * 360 + 330 - outcome * 60,
      timeout: null,
    };
    if (outcome === 2) roll.targetId = neighborId(room, 1);
    if (outcome === 3) roll.targetId = neighborId(room, -1);
    room.punishmentRoll = roll;
    broadcast(room);
    roll.timeout = setTimeout(() => {
      if (rooms[room.code] !== room || room.punishmentRoll !== roll || currentPunishmentKey(room) !== key) return;
      roll.status = 'result';
      broadcast(room);
    }, 3800);
  });
  // ---- เปิดไพ่ ----
  socket.on('cards:flip', () => {
    if (!ok('cards')) return;
    const c = room.secret.deck.pop();
    if (!c) return;
    const s = room.state;
    room.state = {
      current: c,
      remaining: room.secret.deck.length,
      flippedBy: nameOf(room, pid),
      history: [c, ...s.history].slice(0, 6),
    };
    broadcast(room);
  });
  socket.on('cards:reset', () => {
    if (!ok('cards')) return;
    initGame(room, 'cards');
    broadcast(room);
  });

  // ---- รอดหรือร่วง ----
  socket.on('survive:pick', i => {
    if (!ok('survive')) return;
    const s = room.state;
    if (s.loser || s.turn !== pid) return;
    if (!Number.isInteger(i) || i < 0 || i >= s.total) return;
    if (s.opened.some(o => o.i === i)) return;

    s.opened.push({ i, name: nameOf(room, pid) });
    if (i === room.secret.bad) {
      s.loser = { id: pid, name: nameOf(room, pid), card: i };
      s.turn = null;
    } else {
      s.turn = nextTurn(room, pid);
    }
    broadcast(room);
  });
  socket.on('survive:skip', () => {
    if (!ok('survive') || room.state.loser) return;
    room.state.turn = nextTurn(room, room.state.turn);
    broadcast(room);
  });
  socket.on('survive:reset', () => {
    if (!ok('survive')) return;
    newSurviveRound(room, room.state.loser?.id);
    broadcast(room);
  });

  // ---- ลูกเต๋า (ตามคิว) ----
  socket.on('dice:roll', () => {
    if (!ok('dice')) return;
    const s = room.state;
    if (s.turn !== pid) return;
    s.value = randomInt(1, 7);
    s.by = nameOf(room, pid);
    s.rollId++;
    s.turn = nextTurn(room, pid);
    broadcast(room);
  });
  socket.on('dice:skip', () => {
    if (!ok('dice')) return;
    room.state.turn = nextTurn(room, room.state.turn);
    broadcast(room);
  });

  // ---- คำเดียวกัน ----
  socket.on('word:pick', idx => {
    if (!ok('word') || room.state.result) return;
    if (![0, 1, 2].includes(idx) || pid in room.secret.picks) return;
    room.secret.picks[pid] = idx;
    room.state.pickedIds = Object.keys(room.secret.picks);
    checkWord(room);
    broadcast(room);
  });
  socket.on('word:next', () => {
    if (!ok('word')) return;
    newWordRound(room);
    broadcast(room);
  });

  // ---- คำต้องห้าม ----
  socket.on('taboo:mode', mode => {
    if (!ok('taboo') || room.state.status !== 'mode' || !room.state.participants.includes(pid)) return;
    const players = activeIds(room);
    if (players.length < 2) return socket.emit('err', 'เกมคำต้องห้ามต้องมีผู้เล่นอย่างน้อย 2 คน');
    room.state.participants = players;
    if (mode === 'random') {
      if (!newTabooRound(room)) return socket.emit('err', 'จำนวนผู้เล่นมากเกินกว่าชุดคำที่มี');
    } else if (mode === 'custom') {
      room.secret.tabooWords = {};
      room.secret.tabooCustomWords = {};
      room.state.mode = 'custom';
      room.state.status = 'setup';
    } else return;
    broadcast(room);
  });
  socket.on('taboo:submitWord', input => {
    if (!ok('taboo') || room.state.status !== 'setup' || !room.state.participants.includes(pid)) return;
    const word = String(input || '').trim().replace(/\s+/g, ' ').slice(0, 40);
    if (!word) return socket.emit('err', 'พิมพ์คำก่อนกดยืนยัน');
    room.secret.tabooCustomWords ||= {};
    if (room.secret.tabooCustomWords[pid]) return;
    room.secret.tabooCustomWords[pid] = word;
    startCustomTabooIfReady(room);
    broadcast(room);
  });
  socket.on('taboo:lose', () => {
    if (!ok('taboo')) return;
    const s = room.state;
    const word = room.secret.tabooWords?.[pid];
    if (s.status !== 'playing' || !s.participants.includes(pid) || !word) return;
    s.losers ||= [];
    s.losers.push({ id: pid, name: nameOf(room, pid), word });
    s.participants = s.participants.filter(id => id !== pid);
    if (s.participants.length === 1) {
      const winnerId = s.participants[0];
      s.status = 'ended';
      s.winner = { id: winnerId, name: nameOf(room, winnerId) };
    } else if (s.participants.length === 0) {
      s.status = 'ended';
      s.winner = null;
    }
    broadcast(room);
  });
  socket.on('taboo:next', () => {
    if (!ok('taboo')) return;
    if (room.state.mode === 'custom') {
      room.secret.tabooWords = {};
      room.secret.tabooCustomWords = {};
      room.state = { roundId: null, participants: activeIds(room), status: 'setup', mode: 'custom', losers: [], winner: null };
    } else if (!newTabooRound(room)) return socket.emit('err', 'ยังไม่มีชุดคำที่รองรับจำนวนผู้เล่นตอนนี้');
    broadcast(room);
  });

  // ---- หยุดเวลา ----
  socket.on('timer:start', () => {
    if (!ok('timer') || room.state.phase === 'running') return;
    startTimerRound(room, nameOf(room, pid));
    broadcast(room);
  });
  socket.on('timer:stop', ms => {
    if (!ok('timer')) return;
    const s = room.state;
    if (s.phase !== 'running' || !s.participants.includes(pid) || pid in room.secret.times) return;
    if (typeof ms !== 'number' || !Number.isFinite(ms) || ms < 0) return;
    if (ms > Date.now() - room.secret.startedAt) return; // กันค่าปลอม
    room.secret.times[pid] = Math.round(ms);
    checkTimer(room);
    broadcast(room);
  });

  // หลุด: เกมเล่นต่อได้ทันที ชื่อค้างไว้ 60 วิเผื่อกลับมา
  socket.on('disconnect', () => {
    if (!room) return;
    const p = room.players[pid];
    if (!p || p.sid !== socket.id) return;
    p.sid = null;
    const r = room, id = pid;
    p.timer = setTimeout(() => {
      if (r.players[id] === p && !p.sid) removePlayer(r, id);
    }, LEAVE_GRACE_MS);
    refresh(room);
    broadcast(room);
  });
});

const START_PORT = Number(process.env.PORT) || 3000;
const PORT_ATTEMPTS = 20;

function listenOnAvailablePort(port, attemptsLeft) {
  const onError = err => {
    if (err.code === 'EADDRINUSE' && attemptsLeft > 0) {
      console.warn(`Port ${port} is busy; trying ${port + 1}...`);
      setTimeout(() => listenOnAvailablePort(port + 1, attemptsLeft - 1), 100);
      return;
    }
    console.error(`Could not start the game server on port ${port}: ${err.message}`);
    process.exitCode = 1;
  };

  server.once('error', onError);
  server.listen(port, () => {
    server.removeListener('error', onError);
    console.log('Running on http://localhost:' + port);
  });
}

listenOnAvailablePort(START_PORT, PORT_ATTEMPTS);

