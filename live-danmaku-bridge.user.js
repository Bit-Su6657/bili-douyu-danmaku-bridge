// ==UserScript==
// @name         B站斗鱼弹幕桥
// @namespace    https://github.com/Bit-Su6657/bili-douyu-danmaku-bridge
// @version      1.0.0
// @description  B站直播弹幕采样，跨标签页同步到斗鱼侧进行滑窗聚类、正则黑名单过滤、爆发检测与自动弹幕发送。
// @author       Bit-Su6657
// @updateURL    https://raw.githubusercontent.com/Bit-Su6657/bili-douyu-danmaku-bridge/main/live-danmaku-bridge.user.js
// @downloadURL  https://raw.githubusercontent.com/Bit-Su6657/bili-douyu-danmaku-bridge/main/live-danmaku-bridge.user.js
// @homepageURL  https://github.com/Bit-Su6657/bili-douyu-danmaku-bridge
// @supportURL   https://github.com/Bit-Su6657/bili-douyu-danmaku-bridge/issues
// @match        https://live.bilibili.com/*
// @match        https://douyu.com/*
// @match        https://www.douyu.com/*
// @run-at       document-idle
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_addValueChangeListener
// @grant        GM_info
// ==/UserScript==

(function () {
  'use strict';

  const IS_DOUYU = /(^|\.)douyu\.com$/i.test(location.hostname);
  const STORAGE = {
    rooms: 'dbp:rooms:v1',
    config: 'dbp:config:v1',
    roomStatus: (roomId) => `dbp:room:${roomId}:status:v1`,
    roomLatest: (roomId) => `dbp:room:${roomId}:latest:v1`,
    roomSlot: (roomId, slot) => `dbp:room:${roomId}:slot:${slot}:v1`,
    roomSnapshot: (roomId) => `dbp:room:${roomId}:snapshot:v1`,
  };
  const BRIDGE_BATCH_SLOTS = 16;
  const BRIDGE_MAX_WINDOW_SEC = 120;
  const BRIDGE_CLUSTER_WINDOW_SEC = 120;
  const BRIDGE_BUFFER_MS = 150 * 1000;
  const BRIDGE_BURST_FLUSH_MS = 100;
  const BRIDGE_IDLE_FLUSH_MS = 500;
  const BRIDGE_MAX_BATCH = 50;
  const BRIDGE_BURST_HOLD_MS = 3000;
  const BRIDGE_HEARTBEAT_MS = 2000;
  const BRIDGE_SNAPSHOT_MS = 5000;
  const BRIDGE_RENDER_MS = 200;
  const BRIDGE_AGGREGATE_REFRESH_MS = 250;
  const BRIDGE_BURST_CHECK_MS = 500;
  const DEFAULT_CONFIG = {
    schemaVersion: 2,
    windowSec: 10,
    clusterMode: 'simple',
    clusterRule: { type: 'ordered-overlap', options: { minLength: 2 } },
    similarity: 0.8,
    updatedAt: 0,
    updatedBy: '',
    send: {
      sourceMode: 'top1',
      topN: 5,
      strategy: 'fixed',
      minIntervalMs: 10000,
      maxIntervalMs: 20000,
      prefix: '',
      suffix: '',
      customText: '',
      blacklist: '',
      maxLength: 50,
      burst: {
        recentSec: 3,
        baselineSec: 30,
        minCount: 4,
        minLift: 2.5,
        minShareDelta: 0.1,
        confirmCount: 2,
        cooldownSec: 15,
      },
    },
  };

  if (IS_DOUYU) {
    initDouyuBridge();
    return;
  }

  const MIN_WINDOW_MS = 1 * 1000;
  const MAX_WINDOW_MS = 10 * 60 * 1000;
  const BUFFER_GRACE_MS = 15 * 1000;
  const RENDER_INTERVAL_MS = 100;
  const TOP_LIMIT = 20;
  const MAX_ARRIVAL_SAMPLES = 200000;
  const MAX_MUTATION_BATCHES = 5000;
  const METRIC_WINDOWS_MS = [100, 200, 250, 500, 1000];

  const SELECTORS = [
    '.chat-item.danmaku-item',
    '[class*="chat-item"][class*="danmaku-item"]',
  ];

  const CHAT_CONTAINER_SELECTORS = [
    '#chat-items',
    '.chat-history-list',
    '.chat-items',
    '.chat-item.danmaku-item',
    '[class*="chat-history"]',
  ];

  function hasChatContainer() {
    return CHAT_CONTAINER_SELECTORS.some((selector) => document.querySelector(selector));
  }

  function claimPanelOwnership() {
    try {
      const topWindow = window.top || window;
      if (topWindow.__dbpBridgeSamplerOwner && topWindow.__dbpBridgeSamplerOwner !== window) return false;
      topWindow.__dbpBridgeSamplerOwner = window;
    } catch (error) {
      // Cross-origin frames cannot share a top-level marker.
    }

    if (window.__dbpBridgeSamplerStarted) return false;
    window.__dbpBridgeSamplerStarted = true;
    return true;
  }

  function waitForChatContainer(callback, deadline = Date.now() + 30000) {
    if (hasChatContainer()) {
      callback();
      return;
    }
    if (Date.now() >= deadline) return;
    setTimeout(() => waitForChatContainer(callback, deadline), 500);
  }

  function makeDraggablePanel(host, handle, options = {}) {
    if (!host || !handle) return;
    let dragging = false;
    let moved = false;
    let startX = 0;
    let startY = 0;
    let startLeft = 0;
    let startTop = 0;
    const dragThreshold = Math.max(0, Number(options.dragThreshold) || 0);
    handle.style.cursor = 'move';
    handle.addEventListener('pointerdown', (event) => {
      if (event.button !== 0) return;
      if (!options.allowInteractiveHandle && event.target && event.target.closest && event.target.closest('button, input, select, textarea')) return;
      const rect = host.getBoundingClientRect();
      host.style.left = `${rect.left}px`;
      host.style.top = `${rect.top}px`;
      host.style.right = 'auto';
      host.style.bottom = 'auto';
      dragging = true;
      moved = false;
      startX = event.clientX;
      startY = event.clientY;
      startLeft = rect.left;
      startTop = rect.top;
      handle.setPointerCapture?.(event.pointerId);
      event.preventDefault();
    });
    handle.addEventListener('pointermove', (event) => {
      if (!dragging) return;
      const dx = event.clientX - startX;
      const dy = event.clientY - startY;
      if (!moved && Math.hypot(dx, dy) < dragThreshold) return;
      moved = true;
      const width = host.offsetWidth;
      const height = host.offsetHeight;
      const maxLeft = Math.max(0, window.innerWidth - width);
      const maxTop = Math.max(0, window.innerHeight - height);
      const left = Math.min(maxLeft, Math.max(0, startLeft + dx));
      const top = Math.min(maxTop, Math.max(0, startTop + dy));
      host.style.left = `${left}px`;
      host.style.top = `${top}px`;
    });
    const stopDragging = (event) => {
      const wasDragging = dragging;
      const wasMoved = moved;
      dragging = false;
      try { handle.releasePointerCapture?.(event.pointerId); } catch (error) { /* ignore */ }
      if (!wasDragging) return;
      if (!wasMoved && event.type === 'pointerup' && typeof options.onClick === 'function') {
        options.onClick(event);
      } else if (wasMoved && typeof options.onDrop === 'function') {
        options.onDrop(event);
      }
    };
    handle.addEventListener('pointerup', stopDragging);
    handle.addEventListener('pointercancel', stopDragging);
  }

  const state = {
    records: [],
    seenIds: new Set(),
    sessionStartedAt: Date.now(),
    totalCaptured: 0,
    metricsReady: false,
    arrivalTs: [],
    mutationBatches: [],
    windowMs: 60 * 1000,
    paused: false,
    roomId: '',
    firstAt: 0,
    lastPruneAt: 0,
    observer: null,
    renderTimer: null,
    refs: null,
    bridgeSeq: 0,
    bridgeSession: '',
    pendingEvents: [],
    flushTimer: null,
    flushAt: 0,
    burstUntil: 0,
    lastSnapshotAt: 0,
    lastStatusAt: 0,
    bridgeRoomRegistered: false,
    bridgeInitial: false,
    heartbeatTimer: null,
  };

  function getRoomId() {
    const match = location.pathname.match(/(\d+)/);
    return match ? match[1] : '';
  }

  function findItems(root) {
    const items = new Set();
    for (const selector of SELECTORS) {
      try {
        if (root.nodeType === 1 && root.matches(selector)) items.add(root);
        root.querySelectorAll?.(selector).forEach((el) => items.add(el));
      } catch (error) {
        console.warn('[DBP Sampler] selector failed:', selector, error);
      }
    }
    return [...items];
  }

  function fallbackId(record) {
    return `${record.uid}|${record.ts}|${record.text}`;
  }

  function parseItem(el) {
    const dataset = el.dataset || {};
    const type = dataset.type;
    if (type !== undefined && type !== '' && type !== '0') return null;

    const text = (dataset.danmaku || '').trim();
    if (!text) return null;

    const tsSeconds = Number(dataset.ts || dataset.timestamp);
    const ts = Number.isFinite(tsSeconds) && tsSeconds > 0
      ? tsSeconds * 1000
      : Date.now();

    const record = {
      id: dataset.id_str || '',
      text,
      uid: dataset.uid || '',
      uname: dataset.uname || '',
      ts,
      capturedAt: Date.now(),
    };

    if (!record.id) record.id = fallbackId(record);
    return record;
  }

  function capture(el) {
    if (state.paused || !el || el.nodeType !== 1) return;

    const record = parseItem(el);
    if (!record || state.seenIds.has(record.id)) return;
    record.at = state.bridgeInitial && record.ts ? record.ts : record.capturedAt;
    state.seenIds.add(record.id);
    state.records.push(record);
    state.totalCaptured += 1;
    if (state.metricsReady) {
      state.arrivalTs.push(record.capturedAt);
      if (state.arrivalTs.length > MAX_ARRIVAL_SAMPLES) {
        state.arrivalTs.splice(0, state.arrivalTs.length - MAX_ARRIVAL_SAMPLES);
      }
    }

    if (!state.firstAt) state.firstAt = record.at;
    queueBridgeEvent(record);
    prune();
    markDirty();
  }

  function scan(root) {
    findItems(root).forEach(capture);
  }

  function prune() {
    const now = Date.now();
    if (now - state.lastPruneAt < 5000) return;
    state.lastPruneAt = now;

    const cutoff = now - MAX_WINDOW_MS - BUFFER_GRACE_MS;
    if (state.records.length && state.records[0].at < cutoff) {
      state.records = state.records.filter((record) => record.at >= cutoff);
      state.seenIds = new Set(state.records.map((record) => record.id));
      state.firstAt = state.records.length ? state.records[0].at : 0;
    }
  }

  function reset() {
    state.records = [];
    state.seenIds = new Set();
    state.sessionStartedAt = Date.now();
    state.totalCaptured = 0;
    state.metricsReady = true;
    state.arrivalTs = [];
    state.mutationBatches = [];
    state.firstAt = 0;
    state.pendingEvents = [];
    state.bridgeSeq = 0;
    state.bridgeSession = `${Date.now()}-${Math.random().toString(36).slice(2)}`;
    state.burstUntil = 0;
    state.lastSnapshotAt = 0;
    state.lastStatusAt = 0;
    state.bridgeRoomRegistered = false;
    state.bridgeInitial = false;
    if (state.flushTimer) {
      clearTimeout(state.flushTimer);
      state.flushTimer = null;
    }
    state.flushAt = 0;
    render();
  }

  function countRecentArrivals(now) {
    let count = 0;
    for (let i = state.arrivalTs.length - 1; i >= 0; i -= 1) {
      if (now - state.arrivalTs[i] <= 1000) count += 1;
      else break;
    }
    return count;
  }

  function registerBridgeRoom() {
    if (!state.roomId || state.bridgeRoomRegistered) return;
    const rooms = GM_getValue(STORAGE.rooms, []);
    const safeRooms = Array.isArray(rooms) ? rooms : [];
    if (!safeRooms.includes(state.roomId)) {
      safeRooms.push(state.roomId);
      GM_setValue(STORAGE.rooms, safeRooms);
    }
    state.bridgeRoomRegistered = true;
  }

  function scheduleBridgeFlush(force = false) {
    if (!state.pendingEvents.length) return;
    const now = Date.now();
    const delay = now < state.burstUntil
      ? BRIDGE_BURST_FLUSH_MS
      : BRIDGE_IDLE_FLUSH_MS;
    const desiredAt = now + delay;
    if (state.flushTimer) {
      if (!force || state.flushAt <= desiredAt) return;
      clearTimeout(state.flushTimer);
      state.flushTimer = null;
    }
    state.flushAt = desiredAt;
    state.flushTimer = setTimeout(() => {
      state.flushTimer = null;
      state.flushAt = 0;
      flushBridgeEvents();
    }, delay);
  }

  function flushBridgeEvents() {
    if (!state.roomId || !state.pendingEvents.length) return;
    if (state.flushTimer) {
      clearTimeout(state.flushTimer);
      state.flushTimer = null;
    }
    state.flushAt = 0;
    const events = state.pendingEvents.splice(0, state.pendingEvents.length);
    const seq = state.bridgeSeq + 1;
    state.bridgeSeq = seq;
    if (!state.bridgeSession) state.bridgeSession = `${Date.now()}-${Math.random().toString(36).slice(2)}`;
    const slot = seq % BRIDGE_BATCH_SLOTS;
    const emittedAt = Date.now();
    GM_setValue(STORAGE.roomSlot(state.roomId, slot), {
      roomId: state.roomId,
      sessionId: state.bridgeSession,
      seq,
      slot,
      events,
      emittedAt,
    });
    GM_setValue(STORAGE.roomLatest(state.roomId), {
      roomId: state.roomId,
      sessionId: state.bridgeSession,
      seq,
      slot,
      count: events.length,
      emittedAt,
      bufferFrom: events[0].at,
      bufferTo: events[events.length - 1].at,
    });
    scheduleBridgeFlush();
  }

  function queueBridgeEvent(record) {
    if (!state.roomId) return;
    state.pendingEvents.push({
      id: record.id,
      roomId: state.roomId,
      ts: record.ts,
      at: record.at,
      text: record.text,
    });
    const now = Date.now();
    if (countRecentArrivals(now) >= 20 || state.pendingEvents.length >= 10) {
      state.burstUntil = now + BRIDGE_BURST_HOLD_MS;
      scheduleBridgeFlush(true);
    }
    if (state.pendingEvents.length >= BRIDGE_MAX_BATCH) {
      flushBridgeEvents();
      return;
    }
    scheduleBridgeFlush();
  }

  function publishBridgeSnapshot() {
    if (!state.roomId || !state.records.length) return;
    const cutoff = Date.now() - BRIDGE_BUFFER_MS;
    const events = state.records
      .filter((record) => record.at >= cutoff)
      .slice(-5000)
      .map((record) => ({
        id: record.id,
        roomId: state.roomId,
        ts: record.ts,
        at: record.at,
        text: record.text,
      }));
    GM_setValue(STORAGE.roomSnapshot(state.roomId), {
      roomId: state.roomId,
      sessionId: state.bridgeSession,
      seq: state.bridgeSeq,
      events,
      emittedAt: Date.now(),
      bufferFrom: events.length ? events[0].at : 0,
      bufferTo: events.length ? events[events.length - 1].at : 0,
    });
    state.lastSnapshotAt = Date.now();
  }

  function publishBridgeStatus() {
    if (!state.roomId) return;
    registerBridgeRoom();
    const cutoff = Date.now() - BRIDGE_BUFFER_MS;
    const events = state.records.filter((record) => record.at >= cutoff);
    GM_setValue(STORAGE.roomStatus(state.roomId), {
      roomId: state.roomId,
      sessionId: state.bridgeSession,
      lastSeen: Date.now(),
      seq: state.bridgeSeq,
      captured: state.totalCaptured,
      bufferCount: events.length,
      bufferFrom: events.length ? events[0].at : 0,
      bufferTo: events.length ? events[events.length - 1].at : 0,
    });
    state.lastStatusAt = Date.now();
  }

  let dirty = true;

  function markDirty() {
    dirty = true;
  }

  function computeStats() {
    const now = Date.now();
    const cutoff = now - state.windowMs;
    const windowRecords = state.records.filter((record) => record.at >= cutoff);
    const counts = new Map();

    for (const record of windowRecords) {
      counts.set(record.text, (counts.get(record.text) || 0) + 1);
    }

    const top = [...counts.entries()]
      .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0], 'zh-CN'))
      .slice(0, TOP_LIMIT);

    const coveredMs = state.firstAt
      ? Math.min(state.windowMs, Math.max(0, now - state.firstAt))
      : 0;

    return {
      total: state.records.length,
      windowCount: windowRecords.length,
      uniqueTexts: counts.size,
      perMinute: coveredMs > 0 ? (windowRecords.length * 60000) / coveredMs : 0,
      coveredMs,
      top,
    };
  }

  function percentile(sorted, p) {
    if (!sorted.length) return 0;
    const index = Math.min(
      sorted.length - 1,
      Math.max(0, Math.ceil((p / 100) * sorted.length) - 1),
    );
    return sorted[index];
  }

  function statsForNumbers(values) {
    const sorted = [...values].sort((a, b) => a - b);
    return {
      count: sorted.length,
      min: sorted.length ? sorted[0] : 0,
      p50: percentile(sorted, 50),
      p90: percentile(sorted, 90),
      p99: percentile(sorted, 99),
      max: sorted.length ? sorted[sorted.length - 1] : 0,
    };
  }

  function maxEventsInWindow(sortedTimes, windowMs) {
    let right = 0;
    let max = 0;
    for (let left = 0; left < sortedTimes.length; left += 1) {
      if (right < left) right = left;
      while (
        right < sortedTimes.length &&
        sortedTimes[right] - sortedTimes[left] <= windowMs
      ) {
        right += 1;
      }
      max = Math.max(max, right - left);
    }
    return max;
  }

  function computeMetrics() {
    const arrivals = [...state.arrivalTs].sort((a, b) => a - b);
    const batches = state.mutationBatches.filter((batch) => !batch.initial);
    const gaps = [];
    for (let i = 1; i < arrivals.length; i += 1) {
      gaps.push(arrivals[i] - arrivals[i - 1]);
    }

    const sameMs = new Map();
    for (const at of arrivals) {
      sameMs.set(at, (sameMs.get(at) || 0) + 1);
    }
    const sameMsGroups = [...sameMs.values()];
    const maxSameMsGroup = sameMsGroups.reduce((max, value) => Math.max(max, value), 0);

    const maxEventsPerWindow = {};
    for (const windowMs of METRIC_WINDOWS_MS) {
      maxEventsPerWindow[`${windowMs}ms`] = maxEventsInWindow(arrivals, windowMs);
    }

    const capturedBatchSizes = batches
      .map((batch) => batch.captured)
      .filter((count) => count > 0);
    const addedBatchSizes = batches
      .map((batch) => batch.addedItems)
      .filter((count) => count > 0);

    let suggestedFlushMs = 1000;
    if ((maxEventsPerWindow['100ms'] || 0) >= 10) suggestedFlushMs = 100;
    else if ((maxEventsPerWindow['200ms'] || 0) >= 15) suggestedFlushMs = 200;
    else if ((maxEventsPerWindow['500ms'] || 0) >= 20) suggestedFlushMs = 500;

    const sortedBatchSizes = [...capturedBatchSizes].sort((a, b) => a - b);
    const suggestedBatchSize = Math.max(
      50,
      Math.min(100, percentile(sortedBatchSizes, 99) * 2 || 50),
    );

    return {
      url: location.href,
      roomId: state.roomId,
      sessionStartedAt: state.sessionStartedAt,
      exportedAt: Date.now(),
      durationMs: Date.now() - state.sessionStartedAt,
      totalCaptured: state.totalCaptured,
      bufferCount: state.records.length,
      arrivalSampleCount: arrivals.length,
      interArrivalMs: {
        ...statsForNumbers(gaps),
        zeroCount: gaps.filter((gap) => gap === 0).length,
      },
      sameMs: {
        groups: sameMsGroups.length,
        groupsWithMultiple: sameMsGroups.filter((count) => count > 1).length,
        maxGroup: maxSameMsGroup,
      },
      maxEventsPerWindow,
      mutationBatches: {
        batches: batches.length,
        nonEmpty: capturedBatchSizes.length,
        removedNodes: batches.reduce(
          (sum, batch) => sum + (batch.removedItems || 0),
          0,
        ),
        captured: statsForNumbers(capturedBatchSizes),
        addedItems: statsForNumbers(addedBatchSizes),
      },
      messageTsResolutionSec: 1,
      suggestion: {
        flushMs: suggestedFlushMs,
        batchSize: suggestedBatchSize,
      },
    };
  }

  function createPanel() {
    const host = document.createElement('div');
    host.id = 'dbp-bridge-sampler-host';
    host.style.cssText = 'position:fixed;right:16px;bottom:16px;z-index:2147483647;';
    const shadow = host.attachShadow({ mode: 'open' });
    shadow.innerHTML = `
      <style>
        :host { all: initial; }
        .panel {
          width: 360px;
          box-sizing: border-box;
          padding: 12px;
          border: 1px solid #3f4652;
          border-radius: 8px;
          background: #171a21;
          color: #e8edf5;
          font: 12px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif;
          box-shadow: 0 10px 30px rgba(0, 0, 0, 0.35);
        }
        .title { display: flex; align-items: center; justify-content: space-between; margin-bottom: 8px; font-size: 14px; font-weight: 700; cursor: move; user-select: none; }
        .room { color: #9da7b5; font-weight: 400; }
        .controls { display: flex; align-items: center; gap: 8px; margin-bottom: 8px; }
        button {
          padding: 5px 9px;
          border: 1px solid #4b5563;
          border-radius: 6px;
          background: #262b34;
          color: #eef2f7;
          cursor: pointer;
        }
        button:hover { background: #323946; }
        input[type="range"] { flex: 1; }
        .stats { display: grid; grid-template-columns: 1fr 1fr; gap: 4px 10px; margin-bottom: 8px; }
        .stat { color: #c9d3e0; }
        .stat b { color: #ffffff; }
        .list { max-height: 250px; overflow: auto; padding-right: 2px; }
        .item { display: grid; grid-template-columns: 28px 1fr 52px; gap: 6px; align-items: center; margin-bottom: 5px; }
        .rank { color: #9da7b5; text-align: right; }
        .text { min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
        .bar-wrap { position: relative; height: 18px; border-radius: 4px; background: #0f1116; overflow: hidden; }
        .bar { position: absolute; inset: 0 auto 0 0; width: 0; background: #2f6f9f; }
        .bar-text { position: relative; z-index: 1; padding-left: 5px; color: #f3f7fb; }
        .count { color: #a7d7a0; text-align: right; }
        .empty { padding: 12px 0; color: #9da7b5; text-align: center; }
        .status { margin-top: 8px; color: #f0c674; }
      </style>
      <div class="panel">
        <div class="title">
          <span>弹幕采样 <span class="room" id="room"></span></span>
          <button id="pause">暂停</button>
        </div>
        <div class="controls">
          <span id="windowLabel">60秒</span>
          <input id="window" type="range" min="1" max="120" step="1" value="60">
        </div>
        <div class="stats">
          <div class="stat">窗口内 <b id="windowCount">0</b> 条</div>
          <div class="stat">约 <b id="perMinute">0</b> 条/分钟</div>
          <div class="stat">独立文本 <b id="uniqueTexts">0</b></div>
          <div class="stat">缓冲区 <b id="total">0</b> 条</div>
        </div>
        <div class="list" id="list"><div class="empty">等待弹幕...</div></div>
        <div class="status" id="status">正在读取聊天区域...</div>
        <div class="controls" style="margin:8px 0 0">
          <button id="export" style="flex:1">复制指标</button>
          <button id="clear" style="flex:1">清空采样</button>
        </div>
      </div>
    `;
    document.documentElement.appendChild(host);
    makeDraggablePanel(host, shadow.querySelector('.title'));

    const refs = {
      room: shadow.getElementById('room'),
      pause: shadow.getElementById('pause'),
      window: shadow.getElementById('window'),
      windowLabel: shadow.getElementById('windowLabel'),
      windowCount: shadow.getElementById('windowCount'),
      perMinute: shadow.getElementById('perMinute'),
      uniqueTexts: shadow.getElementById('uniqueTexts'),
      total: shadow.getElementById('total'),
      list: shadow.getElementById('list'),
      status: shadow.getElementById('status'),
      export: shadow.getElementById('export'),
      clear: shadow.getElementById('clear'),
    };

    refs.pause.addEventListener('click', () => {
      state.paused = !state.paused;
      refs.pause.textContent = state.paused ? '继续' : '暂停';
      refs.status.textContent = state.paused ? '采样已暂停。' : '采样中。';
    });

    refs.window.addEventListener('input', () => {
      state.windowMs = Number(refs.window.value) * 1000;
      refs.windowLabel.textContent = `${refs.window.value}秒`;
      markDirty();
      render();
    });

    refs.clear.addEventListener('click', () => {
      reset();
      refs.status.textContent = '采样数据已清空，继续监听新弹幕。';
    });

    refs.export.addEventListener('click', async () => {
      const text = JSON.stringify(computeMetrics(), null, 2);
      try {
        await navigator.clipboard.writeText(text);
        refs.status.textContent = '采样指标已复制到剪贴板。';
      } catch (error) {
        window.prompt('复制下面的采样指标：', text);
      }
    });

    return refs;
  }

  function render() {
    if (!state.refs || !dirty) return;
    dirty = false;

    const stats = computeStats();
    state.refs.room.textContent = state.roomId ? `#${state.roomId}` : '';
    state.refs.windowCount.textContent = String(stats.windowCount);
    state.refs.perMinute.textContent = stats.perMinute.toFixed(0);
    state.refs.uniqueTexts.textContent = String(stats.uniqueTexts);
    state.refs.total.textContent = String(stats.total);

    if (!stats.top.length) {
      state.refs.list.innerHTML = '<div class="empty">等待弹幕...</div>';
    } else {
      const maxCount = stats.top[0][1];
      const rows = stats.top.map(([text, count], index) => {
        const row = document.createElement('div');
        row.className = 'item';
        const rank = document.createElement('div');
        rank.className = 'rank';
        rank.textContent = String(index + 1);
        const barWrap = document.createElement('div');
        barWrap.className = 'bar-wrap';
        const bar = document.createElement('div');
        bar.className = 'bar';
        bar.style.width = `${Math.max(4, (count / maxCount) * 100)}%`;
        const barText = document.createElement('div');
        barText.className = 'bar-text';
        barText.textContent = text;
        barWrap.append(bar, barText);
        const countEl = document.createElement('div');
        countEl.className = 'count';
        countEl.textContent = String(count);
        row.append(rank, barWrap, countEl);
        return row;
      });
      state.refs.list.replaceChildren(...rows);
    }

    const coveredSeconds = Math.round(stats.coveredMs / 1000);
    const bridgeNote = state.bridgeSeq ? ` | 已同步 ${state.bridgeSeq} 批` : '';
    state.refs.status.textContent = state.paused
      ? `已暂停，当前覆盖 ${coveredSeconds} 秒。${bridgeNote}`
      : `采样中，当前覆盖 ${coveredSeconds} 秒。${bridgeNote}`;
  }

  function recordMutationBatch(batch) {
    state.mutationBatches.push({
      at: Date.now(),
      addedItems: 0,
      changedItems: 0,
      removedItems: 0,
      captured: 0,
      ...batch,
    });
    if (state.mutationBatches.length > MAX_MUTATION_BATCHES) {
      state.mutationBatches.splice(0, state.mutationBatches.length - MAX_MUTATION_BATCHES);
    }
  }

  function startObserver() {
    if (!document.body) {
      setTimeout(startObserver, 500);
      return;
    }

    state.bridgeSession = `${Date.now()}-${Math.random().toString(36).slice(2)}`;

    state.observer = new MutationObserver((mutations) => {
      const before = state.totalCaptured;
      let addedItems = 0;
      let changedItems = 0;
      let removedItems = 0;

      for (const mutation of mutations) {
        if (mutation.type === 'attributes') {
          changedItems += 1;
          capture(mutation.target);
        } else if (mutation.type === 'characterData') {
          changedItems += 1;
          const item = mutation.target.parentElement?.closest?.('.chat-item.danmaku-item');
          if (item) capture(item);
        } else {
          removedItems += mutation.removedNodes.length;
          for (const node of mutation.addedNodes) {
            const items = findItems(node);
            addedItems += items.length;
            items.forEach(capture);
          }
        }
      }

      recordMutationBatch({
        addedItems,
        changedItems,
        removedItems,
        captured: state.totalCaptured - before,
      });
    });

    state.observer.observe(document.body, {
      childList: true,
      subtree: true,
      attributes: true,
      attributeFilter: ['data-id_str', 'data-danmaku', 'data-ts', 'data-timestamp'],
      characterData: true,
    });

    const initialItems = findItems(document.body);
    const initialBefore = state.totalCaptured;
    state.bridgeInitial = true;
    initialItems.forEach(capture);
    recordMutationBatch({
      initial: true,
      addedItems: initialItems.length,
      captured: state.totalCaptured - initialBefore,
    });
    state.bridgeInitial = false;
    state.metricsReady = true;
    publishBridgeStatus();
    publishBridgeSnapshot();

    state.renderTimer = setInterval(() => {
      const nextRoomId = getRoomId();
      if (nextRoomId !== state.roomId) {
        flushBridgeEvents();
        state.roomId = nextRoomId;
        reset();
        publishBridgeStatus();
        publishBridgeSnapshot();
      }
      const now = Date.now();
      if (now - state.lastStatusAt >= BRIDGE_HEARTBEAT_MS) publishBridgeStatus();
      if (now - state.lastSnapshotAt >= BRIDGE_SNAPSHOT_MS) publishBridgeSnapshot();
      prune();
      render();
    }, RENDER_INTERVAL_MS);

    window.addEventListener('beforeunload', () => {
      flushBridgeEvents();
    });
  }

  waitForChatContainer(() => {
    if (document.getElementById('dbp-bridge-sampler-host')) return;
    if (!claimPanelOwnership()) return;
    state.roomId = getRoomId();
    state.refs = createPanel();
    startObserver();
  });

  function normalizeBurstConfig(value) {
    const raw = value && typeof value === 'object' ? value : {};
    const recentSecNumber = Number(raw.recentSec);
    const recentSec = Number.isFinite(recentSecNumber) ? Math.max(1, Math.min(30, recentSecNumber)) : DEFAULT_CONFIG.send.burst.recentSec;
    const baselineSecNumber = Number(raw.baselineSec);
    const baselineSec = Math.max(recentSec + 5, Number.isFinite(baselineSecNumber) ? Math.min(120, baselineSecNumber) : DEFAULT_CONFIG.send.burst.baselineSec);
    return {
      recentSec,
      baselineSec,
      minCount: Math.max(1, Math.min(100, Number(raw.minCount) || DEFAULT_CONFIG.send.burst.minCount)),
      minLift: Math.max(1, Math.min(20, Number(raw.minLift) || DEFAULT_CONFIG.send.burst.minLift)),
      minShareDelta: Number.isFinite(Number(raw.minShareDelta)) ? Math.max(0, Math.min(1, Number(raw.minShareDelta))) : DEFAULT_CONFIG.send.burst.minShareDelta,
      confirmCount: Math.max(1, Math.min(10, Number(raw.confirmCount) || DEFAULT_CONFIG.send.burst.confirmCount)),
      cooldownSec: Number.isFinite(Number(raw.cooldownSec)) ? Math.max(0, Math.min(300, Number(raw.cooldownSec))) : DEFAULT_CONFIG.send.burst.cooldownSec,
    };
  }

  function normalizeSendConfig(value) {
    const raw = value && typeof value === 'object' ? value : {};
    const safeRaw = { ...raw };
    delete safeRaw.durationMin;
    delete safeRaw.maxCount;
    delete safeRaw.dryRun;
    const minIntervalMs = Math.max(1000, Number(raw.minIntervalMs) || DEFAULT_CONFIG.send.minIntervalMs);
    const maxIntervalMs = Math.max(minIntervalMs, Number(raw.maxIntervalMs) || DEFAULT_CONFIG.send.maxIntervalMs);
    return {
      ...DEFAULT_CONFIG.send,
      ...safeRaw,
      sourceMode: ['top1', 'rotate', 'random', 'custom'].includes(raw.sourceMode) ? raw.sourceMode : DEFAULT_CONFIG.send.sourceMode,
      topN: Math.max(1, Math.min(50, Number(raw.topN) || DEFAULT_CONFIG.send.topN)),
      strategy: raw.strategy === 'hybrid' ? 'hybrid' : 'fixed',
      minIntervalMs,
      maxIntervalMs,
      burst: normalizeBurstConfig(raw.burst),
      prefix: String(raw.prefix || ''),
      suffix: String(raw.suffix || ''),
      customText: String(raw.customText || ''),
      blacklist: String(raw.blacklist || ''),
      maxLength: Math.max(5, Math.min(200, Number(raw.maxLength) || DEFAULT_CONFIG.send.maxLength)),
    };
  }

  function normalizeBridgeConfig(value) {
    const raw = value && typeof value === 'object' ? value : {};
    const schemaVersion = Number(raw.schemaVersion) || 1;
    const clusterMode = schemaVersion < 2
      ? 'simple'
      : (raw.clusterMode === 'simple' ? 'simple' : 'exact');
    return {
      ...DEFAULT_CONFIG,
      ...raw,
      schemaVersion: 2,
      windowSec: Math.max(
        1,
        Math.min(BRIDGE_MAX_WINDOW_SEC, Number(raw.windowSec) || DEFAULT_CONFIG.windowSec),
      ),
      clusterMode,
      clusterRule: raw.clusterRule && typeof raw.clusterRule === 'object' ? raw.clusterRule : { type: clusterMode === 'simple' ? 'ordered-overlap' : 'exact', options: { minLength: 2 } },
      similarity: Math.max(
        0,
        Math.min(1, Number(raw.similarity) || DEFAULT_CONFIG.similarity),
      ),
      send: normalizeSendConfig(raw.send),
    };
  }

  function initDouyuBridge() {
    if (window.top !== window.self) return;
    if (document.getElementById('dbp-douyu-host') || window.__dbpDouyuStarted) return;
    window.__dbpDouyuStarted = true;
    const douyu = {
      rooms: new Map(),
      subscribed: new Set(),
      listeners: [],
      config: normalizeBridgeConfig(GM_getValue(STORAGE.config, null)),
      refs: null,
      renderTimer: null,
      pollTimer: null,
      dirty: true,
      dataRevision: 0,
      aggregateCache: null,
      clusterBaseCache: null,
      sendUiEditing: false,
      ui: {
        minimized: false,
        immersive: false,
        panelLeft: null,
        panelTop: null,
        launcherLeft: null,
        launcherTop: null,
      },
      send: {
        running: false,
        timer: null,
        inFlight: false,
        sentCount: 0,
        cursor: 0,
        lastText: '',
        lastResult: '',
        lastDelayMs: 0,
        lastSentAt: 0,
        nextAt: 0,
      },
      burst: {
        timer: null,
        tracks: new Map(),
        topCandidate: null,
        status: '',
      },
      debug: {
        running: false,
        timer: null,
        tracks: new Map(),
        candidates: [],
        top: null,
        status: '',
        lastSimulatedAt: 0,
        lastSimulatedText: '',
        simulatedCount: 0,
      },
    };
    const addValueChangeListener =
      typeof GM_addValueChangeListener === 'function'
        ? GM_addValueChangeListener
        : () => 0;
    function roomList() {
      const value = GM_getValue(STORAGE.rooms, []);
      return Array.isArray(value) ? value.map(String) : [];
    }
    function ensureRoom(roomId) {
      let room = douyu.rooms.get(roomId);
      if (!room) {
        room = { roomId, sessionId: '', events: [], seenIds: new Set(), lastSeq: 0, lastSeen: 0, status: null };
        douyu.rooms.set(roomId, room);
      }
      return room;
    }
    function syncSession(room, sessionId) {
      if (!sessionId || sessionId === room.sessionId) return;
      room.sessionId = sessionId;
      room.events = [];
      room.seenIds = new Set();
      room.lastSeq = 0;
      douyu.dataRevision += 1;
      douyu.aggregateCache = null;
      douyu.clusterBaseCache = null;
      douyu.dirty = true;
    }

    function eventId(event) {
      return String(event.id || `${event.roomId}|${event.at}|${event.text}`);
    }
    function mergeEvents(roomId, events) {
      const room = ensureRoom(roomId);
      let changed = false;
      for (const event of events || []) {
        if (!event) continue;
        const id = eventId(event);
        if (room.seenIds.has(id)) continue;
        room.seenIds.add(id);
        room.events.push({ id, roomId, ts: Number(event.ts) || 0, at: Number(event.at) || Date.now(), text: String(event.text || '').trim() });
        changed = true;
      }
      if (!changed) return;
      room.events.sort((a, b) => a.at - b.at);
      const cutoff = Date.now() - BRIDGE_BUFFER_MS;
      if (room.events.length && room.events[0].at < cutoff) {
        room.events = room.events.filter((event) => event.at >= cutoff);
        room.seenIds = new Set(room.events.map((event) => event.id));
      }
      douyu.dataRevision += 1;
      douyu.aggregateCache = null;
      douyu.clusterBaseCache = null;
      douyu.dirty = true;
    }
    function readSlot(roomId, seq) {
      const slot = seq % BRIDGE_BATCH_SLOTS;
      const batch = GM_getValue(STORAGE.roomSlot(roomId, slot), null);
      if (!batch || Number(batch.seq) !== seq) return false;
      const room = ensureRoom(roomId);
      if (batch.sessionId && room.sessionId && batch.sessionId !== room.sessionId) return false;
      mergeEvents(roomId, batch.events || []);
      return true;
    }
    function readSnapshot(roomId) {
      const snapshot = GM_getValue(STORAGE.roomSnapshot(roomId), null);
      if (!snapshot) return;
      const room = ensureRoom(roomId);
      syncSession(room, snapshot.sessionId);
      mergeEvents(roomId, snapshot.events || []);
      room.lastSeq = Math.max(room.lastSeq, Number(snapshot.seq) || 0);
      room.lastSeen = Number(snapshot.emittedAt) || room.lastSeen;
    }
    function readLatest(roomId) {
      const latest = GM_getValue(STORAGE.roomLatest(roomId), null);
      if (!latest) return;
      const room = ensureRoom(roomId);
      syncSession(room, latest.sessionId);
      const seq = Number(latest.seq) || 0;
      room.lastSeen = Number(latest.emittedAt) || room.lastSeen;
      if (seq <= room.lastSeq) return;
      const start = Math.max(room.lastSeq + 1, seq - BRIDGE_BATCH_SLOTS + 1);
      let complete = true;
      for (let current = start; current <= seq; current += 1) {
        if (!readSlot(roomId, current)) { complete = false; break; }
      }
      if (!complete) readSnapshot(roomId);
      room.lastSeq = Math.max(room.lastSeq, seq);
    }
    function readStatus(roomId) {
      const status = GM_getValue(STORAGE.roomStatus(roomId), null);
      if (!status) return;
      const room = ensureRoom(roomId);
      syncSession(room, status.sessionId);
      room.status = status;
      room.lastSeen = Number(status.lastSeen) || room.lastSeen;
    }
    function subscribeRoom(roomId) {
      if (douyu.subscribed.has(roomId)) return;
      douyu.subscribed.add(roomId);
      douyu.listeners.push(addValueChangeListener(STORAGE.roomLatest(roomId), () => {
        readLatest(roomId); douyu.dirty = true;
      }));
      douyu.listeners.push(addValueChangeListener(STORAGE.roomSnapshot(roomId), () => {
        readSnapshot(roomId); douyu.dirty = true;
      }));
    }
    function refreshRegistry() {
      for (const roomId of roomList()) {
        ensureRoom(roomId); subscribeRoom(roomId); readStatus(roomId); readLatest(roomId);
      }
      for (const room of douyu.rooms.values()) if (!room.events.length) readSnapshot(room.roomId);
    }
    function normalizeClusterText(text) {
      let value = String(text || '');
      try { value = value.normalize('NFKC'); } catch (error) { /* ignore */ }
      value = value.replace(/[\u200B-\u200D\uFEFF]/g, '').replace(/\s+/g, '').toLowerCase();
      try { value = value.replace(/\p{P}/gu, ''); } catch (error) { /* ignore */ }
      return value || String(text || '').trim();
    }

    function graphemes(text) {
      try {
        if (typeof Intl !== 'undefined' && Intl.Segmenter) {
          return [...new Intl.Segmenter(undefined, { granularity: 'grapheme' }).segment(text)]
            .map((part) => part.segment);
        }
      } catch (error) { /* ignore */ }
      return Array.from(text);
    }

    function shortestCycle(text) {
      const units = graphemes(text);
      const length = units.length;
      if (length <= 1) return text;
      const lps = new Array(length).fill(0);
      for (let i = 1; i < length; i += 1) {
        let j = lps[i - 1];
        while (j > 0 && units[i] !== units[j]) j = lps[j - 1];
        if (units[i] === units[j]) j += 1;
        lps[i] = j;
      }
      const period = length - lps[length - 1];
      if (period > 0 && period < length && length % period === 0) {
        return units.slice(0, period).join('');
      }
      return text;
    }

    function lcsLength(left, right) {
      let previous = new Array(right.length + 1).fill(0);
      for (let i = 1; i <= left.length; i += 1) {
        const current = new Array(right.length + 1).fill(0);
        for (let j = 1; j <= right.length; j += 1) {
          current[j] = left[i - 1] === right[j - 1]
            ? previous[j - 1] + 1
            : Math.max(previous[j], current[j - 1]);
        }
        previous = current;
      }
      return previous[right.length];
    }

    function overlapUpperBound(left, right) {
      const remaining = new Map();
      for (const unit of left) remaining.set(unit, (remaining.get(unit) || 0) + 1);
      let shared = 0;
      for (const unit of right) {
        const count = remaining.get(unit) || 0;
        if (!count) continue;
        shared += 1;
        remaining.set(unit, count - 1);
      }
      return shared / Math.max(left.length, right.length, 1);
    }
    function orderedOverlap(leftText, rightText) {
      if (!leftText || !rightText) return 0;
      if (leftText === rightText) return 1;
      const left = graphemes(leftText);
      const right = graphemes(rightText);
      const maxLength = Math.max(left.length, right.length);
      const minLength = Math.min(left.length, right.length);
      if (!maxLength || minLength / maxLength < 0.5) return 0;
      return lcsLength(left, right) / maxLength;
    }

    function clusterExact(records) {
      const counts = new Map();
      for (const record of records) {
        const text = String(record.text || '').trim();
        if (!text) continue;
        counts.set(text, (counts.get(text) || 0) + 1);
      }
      return [...counts.entries()]
        .map(([text, count]) => ({ key: text, text, count, exactCount: count, members: [{ text, count }] }))
        .sort((a, b) => b.count - a.count || a.text.localeCompare(b.text, 'zh-CN'));
    }

    function clusterOrderedOverlap(records, config) {
      const threshold = Math.max(0, Math.min(1, Number(config.similarity) || 0.8));
      const ruleOptions = config.clusterRule && config.clusterRule.options;
      const minLength = Number(ruleOptions && ruleOptions.minLength)
        || Number(config.clusterRule && config.clusterRule.minLength)
        || 2;
      const counts = new Map();
      for (const record of records) {
        const text = String(record.text || '').trim();
        if (!text) continue;
        const entry = counts.get(text) || { text, count: 0 };
        entry.count += 1;
        counts.set(text, entry);
      }
      const unique = [...counts.values()]
        .sort((a, b) => b.count - a.count || b.text.length - a.text.length);
      const clusters = [];
      const exactClusters = new Map();
      for (const item of unique) {
        const normalized = shortestCycle(normalizeClusterText(item.text));
        const normalizedUnits = graphemes(normalized);
        let best = exactClusters.get(normalized) || null;
        let bestScore = best ? 1 : -1;
        if (!best) {
          for (const cluster of clusters) {
            const minNormalized = Math.min(normalizedUnits.length, cluster.units.length);
            const maxNormalized = Math.max(normalizedUnits.length, cluster.units.length, 1);
            if (minNormalized / maxNormalized < 0.5) continue;
            if (minNormalized < minLength) continue;
            if (overlapUpperBound(normalizedUnits, cluster.units) < threshold) continue;
            const score = orderedOverlap(normalized, cluster.normalized);
            if (score > bestScore) { bestScore = score; best = cluster; }
          }
        }
        if (best && bestScore >= threshold) {
          best.totalCount += item.count;
          best.members.push({ text: item.text, count: item.count });
        } else {
          const cluster = { normalized, units: normalizedUnits, totalCount: item.count, members: [{ text: item.text, count: item.count }] };
          clusters.push(cluster);
          if (!exactClusters.has(normalized)) exactClusters.set(normalized, cluster);
        }
      }
      return clusters.map((cluster) => {
        const members = [...cluster.members].sort((a, b) => b.count - a.count || b.text.length - a.text.length);
        return { key: cluster.normalized, approximate: true, text: members[0].text, count: cluster.totalCount, exactCount: members[0].count, members };
      }).sort((a, b) => b.count - a.count || a.text.localeCompare(b.text, 'zh-CN'));
    }

    function clusterRecords(records, config) {
      if (config.clusterMode === 'simple') return clusterOrderedOverlap(records, config);
      return clusterExact(records);
    }
    function burstKeyForText(text) {
      return shortestCycle(normalizeClusterText(String(text || '').trim()));
    }

    function collectWindowRecords(windowSec) {


      const now = Date.now();
      const windowMs = windowSec * 1000;
      const cutoff = now - windowMs;
      const records = [];
      const perRoom = new Map();
      let expiresAt = Infinity;
      for (const room of douyu.rooms.values()) {
        const filtered = room.events.filter((event) => event.at >= cutoff);
        perRoom.set(room.roomId, filtered.length);
        records.push(...filtered);
        for (const event of filtered) expiresAt = Math.min(expiresAt, event.at + windowMs + 1);
      }
      return { records, perRoom, expiresAt, now, windowSec };
    }

    function buildClusterIndex(clusters, allowCanonical = true) {
      const textToKey = new Map();
      const canonicalToKey = new Map();
      for (const cluster of clusters) {
        const clusterKey = cluster.key || burstKeyForText(cluster.text);
        textToKey.set(cluster.text, clusterKey);
        if (allowCanonical) canonicalToKey.set(clusterKey, clusterKey);
        for (const member of cluster.members || []) {
          textToKey.set(member.text, clusterKey);
          if (allowCanonical) canonicalToKey.set(burstKeyForText(member.text), clusterKey);
        }
      }
      return { textToKey, canonicalToKey };
    }

    function countClustersInWindow(records, clusters, allowCanonical = true) {
      const index = buildClusterIndex(clusters, allowCanonical);
      const counts = new Map();
      for (const record of records) {
        const text = String(record.text || '').trim();
        if (!text) continue;
        const key = index.textToKey.get(text) || index.canonicalToKey.get(burstKeyForText(text));
        if (key) counts.set(key, (counts.get(key) || 0) + 1);
      }
      return clusters.map((cluster) => ({
        ...cluster,
        count: counts.get(cluster.key) || 0,
        exactCount: counts.get(cluster.key) || 0,
      })).filter((cluster) => cluster.count > 0).sort((a, b) => b.count - a.count || a.text.localeCompare(b.text, 'zh-CN'));
    }

    function getClusterBase() {
      const config = douyu.config;
      const cacheKey = [
        douyu.dataRevision,
        BRIDGE_CLUSTER_WINDOW_SEC,
        config.clusterMode,
        config.similarity,
        JSON.stringify(config.clusterRule || null),
      ].join('|');
      const now = Date.now();
      const cached = douyu.clusterBaseCache;
      if (cached) {
        if (cached.key === cacheKey && now < cached.expiresAt) return cached.result;
        if (now < cached.nextUpdateAt) return cached.result;
      }
      const collected = collectWindowRecords(BRIDGE_CLUSTER_WINDOW_SEC);
      const clusters = clusterRecords(collected.records, config);
      const result = { records: collected.records, clusters, perRoom: collected.perRoom, cacheKey, windowSec: BRIDGE_CLUSTER_WINDOW_SEC };
      let expiresAt = collected.expiresAt;
      if (expiresAt !== Infinity) {
        expiresAt = Math.ceil(expiresAt / BRIDGE_AGGREGATE_REFRESH_MS) * BRIDGE_AGGREGATE_REFRESH_MS;
      }
      douyu.clusterBaseCache = { key: cacheKey, expiresAt, nextUpdateAt: now + BRIDGE_AGGREGATE_REFRESH_MS, result };
      return result;
    }

    function aggregate() {
      const config = douyu.config;
      const base = getClusterBase();
      const cacheKey = [douyu.dataRevision, base.cacheKey, config.windowSec].join('|');
      const now = Date.now();
      const cached = douyu.aggregateCache;
      if (cached) {
        if (cached.key === cacheKey && now < cached.expiresAt) return cached.result;
        if (now < cached.nextUpdateAt) return cached.result;
      }
      const collected = collectWindowRecords(config.windowSec);
      const result = {
        records: collected.records,
        clusters: countClustersInWindow(collected.records, base.clusters, config.clusterMode === 'simple'),
        perRoom: collected.perRoom,
        baseWindowSec: base.windowSec,
      };
      let expiresAt = collected.expiresAt;
      if (expiresAt !== Infinity) {
        expiresAt = Math.ceil(expiresAt / BRIDGE_AGGREGATE_REFRESH_MS) * BRIDGE_AGGREGATE_REFRESH_MS;
      }
      douyu.aggregateCache = { key: cacheKey, expiresAt, nextUpdateAt: now + BRIDGE_AGGREGATE_REFRESH_MS, result };
      return result;
    }
    function writeConfig(partial) {
      douyu.config = normalizeBridgeConfig({ ...douyu.config, ...partial });
      GM_setValue(STORAGE.config, { ...douyu.config, updatedAt: Date.now(), updatedBy: 'douyu' });
      douyu.aggregateCache = null;
      douyu.clusterBaseCache = null;
      douyu.dirty = true;
    }
    function createDouyuPanel() {
    function sendBoxContainsActiveElement() {
      const sendBox = douyu.refs && douyu.refs.sendBox;
      if (!sendBox) return false;
      const root = sendBox.getRootNode && sendBox.getRootNode();
      const active = root && root.activeElement ? root.activeElement : document.activeElement;
      return !!active && sendBox.contains(active);
    }

    function syncSendUI() {
      if (!douyu.refs || !douyu.refs.sendBox) return;
      if (douyu.sendUiEditing || sendBoxContainsActiveElement()) return;
      const cfg = douyu.config.send;
      douyu.refs.sendSource.value = cfg.sourceMode;
      douyu.refs.sendTopNWrap.style.display = ['rotate', 'random'].includes(cfg.sourceMode) ? 'inline-flex' : 'none';
      douyu.refs.sendTopN.value = String(cfg.topN);
      douyu.refs.sendStrategy.value = cfg.strategy;
      douyu.refs.sendMinMs.value = String(cfg.minIntervalMs);
      douyu.refs.sendMaxMs.value = String(cfg.maxIntervalMs);
      douyu.refs.sendBurstRecent.value = String(cfg.burst.recentSec);
      douyu.refs.sendBurstBaseline.value = String(cfg.burst.baselineSec);
      douyu.refs.sendBurstMinCount.value = String(cfg.burst.minCount);
      douyu.refs.sendBurstLift.value = String(cfg.burst.minLift);
      douyu.refs.sendBurstShare.value = String(Math.round(cfg.burst.minShareDelta * 100));
      douyu.refs.sendBurstConfirm.value = String(cfg.burst.confirmCount);
      douyu.refs.sendBurstCooldown.value = String(cfg.burst.cooldownSec);
      douyu.refs.sendPrefix.value = cfg.prefix;
      douyu.refs.sendSuffix.value = cfg.suffix;
      douyu.refs.sendBlacklist.value = cfg.blacklist;
      douyu.refs.sendCustom.value = cfg.customText;
      douyu.refs.sendCustom.style.display = cfg.sourceMode === 'custom' ? 'block' : 'none';
      douyu.refs.sendBurstWrap.style.display = cfg.strategy === 'hybrid' && cfg.sourceMode !== 'custom' ? 'block' : 'none';
    }
    douyu.syncSendUI = syncSendUI;

    function randomSendDelay(min, max) {
      const low = Math.max(1, min);
      const high = Math.max(low, max);
      return Math.floor(Math.random() * (high - low + 1) + low);
    }

    function compileBlacklistRule(value) {
      const source = String(value || '').trim();
      if (!source) return null;
      const compileRegex = (pattern, flags) => {
        const safeFlags = [...new Set(String(flags || '').replace(/[gy]/g, ''))].join('');
        try { return new RegExp(pattern, safeFlags); } catch (error) { return null; }
      };
      const literal = /^\/([\s\S]*)\/([dgimsuvy]*)$/.exec(source);
      if (literal) {
        const regex = compileRegex(literal[1], literal[2]);
        if (regex) return { type: 'regex', regex, source };
      }
      if (/[\\^$.*+?()[\]{}|]/.test(source)) {
        const regex = compileRegex(source, 'i');
        if (regex) return { type: 'regex', regex, source };
      }
      return { type: 'exact', value: source.toLowerCase(), source };
    }

    let sendBlacklistCacheSource = '';
    let sendBlacklistCacheRules = [];
    function getSendBlacklist() {
      const sourceList = String(douyu.config.send.blacklist || '');
      if (sourceList === sendBlacklistCacheSource) return sendBlacklistCacheRules;
      const seen = new Set();
      const rules = [];
      for (const item of sourceList.split(/\r?\n/)) {
        const source = item.trim();
        if (!source || seen.has(source)) continue;
        seen.add(source);
        const rule = compileBlacklistRule(source);
        if (rule) rules.push(rule);
      }
      sendBlacklistCacheSource = sourceList;
      sendBlacklistCacheRules = rules;
      return rules;
    }

    function isBlacklistedText(text, blacklist = getSendBlacklist()) {
      if (!text || !blacklist.length) return false;
      const value = String(text);
      return blacklist.some((rule) => {
        if (rule.type === 'regex') {
          rule.regex.lastIndex = 0;
          return rule.regex.test(value);
        }
        return value.toLowerCase() === rule.value;
      });
    }

    function getSendCandidates() {
      const cfg = douyu.config.send;
      const blacklist = getSendBlacklist();
      if (cfg.sourceMode === 'custom') {
        return cfg.customText.split(/\r?\n/).map((item) => item.trim()).filter(Boolean).filter((item) => !isBlacklistedText(item, blacklist));
      }
      const clusters = aggregate().clusters.filter((cluster) => !isBlacklistedText(cluster.text, blacklist));
      const limit = cfg.sourceMode === 'top1' ? 1 : Math.max(1, Number(cfg.topN) || 1);
      return clusters.slice(0, limit).map((cluster) => cluster.text).filter(Boolean);
    }


    function computeBurstCandidates() {
      const now = Date.now();
      const sendConfig = douyu.config.send;
      const burstConfig = sendConfig.burst;
      const recentSec = Math.max(1, burstConfig.recentSec);
      const baselineSec = Math.max(recentSec + 5, burstConfig.baselineSec);
      const recentMs = recentSec * 1000;
      const baselineMs = baselineSec * 1000;
      const recentStart = now - recentMs;
      const baselineStart = now - baselineMs;
      const clusters = getClusterBase().clusters;
      if (!clusters.length) return [];

      const index = buildClusterIndex(clusters, sendConfig.clusterMode === 'simple');

      const recentCounts = new Map();
      const baselineCounts = new Map();
      let recentTotal = 0;
      let baselineTotal = 0;
      for (const room of douyu.rooms.values()) {
        for (const event of room.events) {
          if (event.at < baselineStart) continue;
          const text = String(event.text || '').trim();
          if (!text) continue;
          const key = index.textToKey.get(text) || index.canonicalToKey.get(burstKeyForText(text));
          if (event.at >= recentStart) {
            recentTotal += 1;
            if (key) recentCounts.set(key, (recentCounts.get(key) || 0) + 1);
          } else {
            baselineTotal += 1;
            if (key) baselineCounts.set(key, (baselineCounts.get(key) || 0) + 1);
          }
        }
      }

      const recentSeconds = Math.max(0.5, recentMs / 1000);
      const baselineSeconds = Math.max(1, (baselineMs - recentMs) / 1000);
      const candidates = clusters.map((cluster) => {
        const key = cluster.key || burstKeyForText(cluster.text);
        const recentCount = recentCounts.get(key) || 0;
        const baselineCount = baselineCounts.get(key) || 0;
        const recentRate = recentCount / recentSeconds;
        const baselineRate = Math.max(baselineCount / baselineSeconds, 0.05);
        const lift = recentRate / baselineRate;
        const recentShare = recentTotal ? recentCount / recentTotal : 0;
        const baselineShare = baselineTotal ? baselineCount / baselineTotal : 0;
        const shareDelta = recentShare - baselineShare;
        const qualifies = recentCount >= burstConfig.minCount
          && lift >= burstConfig.minLift
          && shareDelta >= burstConfig.minShareDelta;
        const score = 0.5 * Math.log2(lift + 1)
          + 0.3 * Math.max(0, shareDelta) * 10
          + 0.2 * Math.log2(recentCount + 1);
        return { key, text: cluster.text, recentCount, baselineCount, lift, shareDelta, recentShare, baselineShare, score, qualifies };
      }).sort((left, right) => right.score - left.score || right.recentCount - left.recentCount);
      const blacklist = getSendBlacklist();
      return candidates.filter((candidate) => !isBlacklistedText(candidate.text, blacklist));
    }

    function stopBurstMonitor() {
      clearInterval(douyu.burst.timer);
      douyu.burst.timer = null;
      douyu.burst.tracks.clear();
      douyu.burst.topCandidate = null;
      douyu.burst.status = '';
    }

    function startBurstMonitor() {
      stopBurstMonitor();
      if (!douyu.send.running || douyu.config.send.strategy !== 'hybrid' || douyu.config.send.sourceMode === 'custom') return;
      douyu.burst.timer = setInterval(updateBurstDetection, BRIDGE_BURST_CHECK_MS);
    }

    function updateBurstDetection() {
      if (!douyu.send.running || douyu.config.send.strategy !== 'hybrid' || douyu.config.send.sourceMode === 'custom') return;
      if (douyu.send.inFlight) return;
      const now = Date.now();
      const cfg = douyu.config.send;
      const candidates = computeBurstCandidates();
      const candidateByKey = new Map(candidates.map((candidate) => [candidate.key, candidate]));
      douyu.burst.topCandidate = candidates[0] || null;

      for (const [key, track] of douyu.burst.tracks) {
        if (!candidateByKey.has(key)) track.hits = 0;
      }
      for (const candidate of candidates) {
        const track = douyu.burst.tracks.get(candidate.key) || { hits: 0, lastHitAt: 0, cooldownUntil: 0, score: 0 };
        if (candidate.qualifies) {
          const consecutive = now - track.lastHitAt <= BRIDGE_BURST_CHECK_MS * 2.5;
          track.hits = consecutive ? track.hits + 1 : 1;
          track.lastHitAt = now;
          track.score = candidate.score;
        } else {
          track.hits = 0;
        }
        douyu.burst.tracks.set(candidate.key, track);
      }

      for (const [key, track] of douyu.burst.tracks) {
        if (now - track.lastHitAt > Math.max(120000, cfg.burst.baselineSec * 1000 * 2) && now >= track.cooldownUntil) {
          douyu.burst.tracks.delete(key);
        }
      }

      const ready = candidates.find((candidate) => {
        const track = douyu.burst.tracks.get(candidate.key);
        return candidate.qualifies && track && track.hits >= cfg.burst.confirmCount && now >= track.cooldownUntil;
      });
      const top = candidates[0] || null;
      if (!ready) {
        if (top && top.qualifies) {
          const track = douyu.burst.tracks.get(top.key);
          douyu.burst.status = `爆发确认 ${top.text} ${Math.min(track ? track.hits : 0, cfg.burst.confirmCount)}/${cfg.burst.confirmCount}`;
        } else {
          const recentSec = Math.max(1, cfg.burst.recentSec);
          douyu.burst.status = top && top.recentCount ? `爆发观察 ${top.text}（${top.recentCount} 条/${recentSec}秒）` : '';
        }
        return;
      }

      const track = douyu.burst.tracks.get(ready.key);
      track.hits = 0;
      track.cooldownUntil = now + cfg.burst.cooldownSec * 1000;
      douyu.burst.status = `爆发触发 ${ready.text}（${ready.lift.toFixed(1)}x，${ready.recentCount} 条）`;
      sendOnce({ burstCandidate: ready });
    }

    function stopDebugSimulation() {
      clearInterval(douyu.debug.timer);
      douyu.debug.timer = null;
      douyu.debug.running = false;
      douyu.debug.tracks.clear();
      douyu.debug.candidates = [];
      douyu.debug.top = null;
      douyu.debug.status = '';
      if (douyu.refs && douyu.refs.debugStart) douyu.refs.debugStart.textContent = '模拟启动';
    }

    function startDebugSimulation() {
      stopDebugSimulation();
      douyu.debug.running = true;
      douyu.debug.lastSimulatedAt = 0;
      douyu.debug.lastSimulatedText = '';
      douyu.debug.simulatedCount = 0;
      douyu.debug.status = '模拟已启动';
      if (douyu.refs && douyu.refs.debugStart) douyu.refs.debugStart.textContent = '停止模拟';
      douyu.debug.timer = setInterval(updateDebugSimulation, BRIDGE_BURST_CHECK_MS);
      updateDebugSimulation();
      render();
    }

    function updateDebugSimulation() {
      if (!douyu.debug.running) return;
      const now = Date.now();
      const cfg = douyu.config.send;
      const candidates = computeBurstCandidates();
      const candidateByKey = new Map(candidates.map((candidate) => [candidate.key, candidate]));

      for (const [key, track] of douyu.debug.tracks) {
        if (!candidateByKey.has(key)) track.hits = 0;
      }
      for (const candidate of candidates) {
        const track = douyu.debug.tracks.get(candidate.key) || { hits: 0, lastHitAt: 0, cooldownUntil: 0, score: 0 };
        if (candidate.qualifies) {
          const consecutive = now - track.lastHitAt <= BRIDGE_BURST_CHECK_MS * 2.5;
          track.hits = consecutive ? track.hits + 1 : 1;
          track.lastHitAt = now;
          track.score = candidate.score;
        } else {
          track.hits = 0;
        }
        douyu.debug.tracks.set(candidate.key, track);
      }

      const ready = candidates.find((candidate) => {
        const track = douyu.debug.tracks.get(candidate.key);
        return candidate.qualifies && track && track.hits >= cfg.burst.confirmCount && now >= track.cooldownUntil;
      });
      douyu.debug.candidates = candidates;
      douyu.debug.top = candidates[0] || null;
      if (!ready) {
        if (douyu.debug.top && douyu.debug.top.qualifies) {
          const track = douyu.debug.tracks.get(douyu.debug.top.key);
          douyu.debug.status = `确认中 ${Math.min(track ? track.hits : 0, cfg.burst.confirmCount)}/${cfg.burst.confirmCount}`;
        } else {
          douyu.debug.status = douyu.debug.top ? '观察中' : '暂无候选';
        }
        updateDebugPanel();
        return;
      }

      const track = douyu.debug.tracks.get(ready.key);
      track.hits = 0;
      track.cooldownUntil = now + cfg.burst.cooldownSec * 1000;
      douyu.debug.lastSimulatedAt = now;
      douyu.debug.lastSimulatedText = ready.text;
      douyu.debug.simulatedCount += 1;
      douyu.debug.status = `模拟将发送：${ready.text}（${ready.lift.toFixed(1)}x）`;
      updateDebugPanel();
    }

    function updateDebugPanel() {
      const refs = douyu.refs;
      if (!refs || !refs.debugSummary || !refs.debugList) return;
      const cfg = douyu.config.send;
      const effectiveRecentSec = Math.max(1, cfg.burst.recentSec);
      const blacklistCount = getSendBlacklist().length;
      refs.debugSummary.textContent = `聚类基底 ${BRIDGE_CLUSTER_WINDOW_SEC} 秒 / 最近 ${effectiveRecentSec} 秒 / 基线 ${cfg.burst.baselineSec} 秒，真实策略：${cfg.strategy === 'hybrid' ? '固定+爆发(可打断)' : '固定周期'}，爆发仅受冷却限制，黑名单 ${blacklistCount} 条，模拟状态：${douyu.debug.running ? '运行中' : '未启动'}，模拟触发 ${douyu.debug.simulatedCount} 次`;
      if (refs.debugStatus) refs.debugStatus.textContent = douyu.debug.status || (douyu.debug.running ? '等待检测' : '未启动');
      if (refs.debugTop) {
        const top = douyu.debug.top;
        const topRate = top ? top.recentCount / effectiveRecentSec : 0;
        refs.debugTop.textContent = top
          ? `TOP ${top.text} | 最近 ${top.recentCount} 条 (${topRate.toFixed(2)}/s) | 基线 ${top.baselineCount} 条 | 放大 ${top.lift.toFixed(2)}x | 占比变化 ${(top.shareDelta * 100).toFixed(1)}% | 分数 ${top.score.toFixed(2)} | 条件 ${top.qualifies ? '通过' : '未通过'}`
          : '暂无候选';
      }
      if (!douyu.debug.candidates.length) {
        refs.debugList.innerHTML = '<div class="empty">模拟启动后显示候选数据。</div>';
        return;
      }
      const rows = douyu.debug.candidates.slice(0, 20).map((candidate) => {
        const track = douyu.debug.tracks.get(candidate.key);
        const cooldownSec = track && track.cooldownUntil > Date.now() ? Math.ceil((track.cooldownUntil - Date.now()) / 1000) : 0;
        const row = document.createElement('div');
        row.className = 'debug-item';
        row.title = `最近 ${candidate.recentCount} 条，基线 ${candidate.baselineCount} 条，最近占比 ${(candidate.recentShare * 100).toFixed(1)}%，基线占比 ${(candidate.baselineShare * 100).toFixed(1)}%`;
        const text = document.createElement('div');
        text.className = 'debug-text';
        text.textContent = candidate.text;
        const metrics = document.createElement('div');
        metrics.className = 'debug-metrics';
        metrics.textContent = `最近 ${candidate.recentCount} / 基线 ${candidate.baselineCount} / ${candidate.lift.toFixed(2)}x / 占比 ${(candidate.shareDelta * 100).toFixed(1)}% / 分数 ${candidate.score.toFixed(2)}`;
        const state = document.createElement('div');
        state.className = candidate.qualifies ? 'debug-state debug-ok' : 'debug-state debug-bad';
        state.textContent = `${candidate.qualifies ? '达标' : '未达标'} · 确认 ${Math.min(track ? track.hits : 0, cfg.burst.confirmCount)}/${cfg.burst.confirmCount}${cooldownSec ? ` · 冷却 ${cooldownSec}s` : ''}`;
        row.append(text, metrics, state);
        return row;
      });
      refs.debugList.replaceChildren(...rows);
    }
    douyu.updateDebugPanel = updateDebugPanel;




    function buildSendMessage(text, cfg) {
      return `${cfg.prefix || ''}${text}${cfg.suffix || ''}`.trim();
    }

    function setChatInputText(input, text) {
      if (input.tagName === 'TEXTAREA') {
        const descriptor = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, 'value');
        if (descriptor && descriptor.set) descriptor.set.call(input, text);
        else input.value = text;
      } else {
        input.innerText = text;
      }
      input.dispatchEvent(new Event('input', { bubbles: true }));
      input.dispatchEvent(new Event('change', { bubbles: true }));
    }

    function triggerDouyuSend(text) {
      const input = document.querySelector('textarea.ChatSend-txt, div.ChatSend-txt');
      const button = document.querySelector('.ChatSend-button');
      if (!input || !button) return { ok: false, reason: '未找到斗鱼聊天输入框或发送按钮' };
      if (input.disabled || button.disabled) return { ok: false, reason: '聊天输入框当前不可用' };
      setChatInputText(input, text);
      button.click();
      return { ok: true, input };
    }

    async function sendOnce(options = {}) {
      const manual = options.manual === true;
      const burstCandidate = options.burstCandidate || null;
      if (!manual && !douyu.send.running) return;
      if (douyu.send.inFlight) return;
      douyu.send.inFlight = true;
      const cfg = douyu.config.send;
      const candidates = burstCandidate ? [] : getSendCandidates();
      if (!burstCandidate && !candidates.length) {
        if (!manual && cfg.strategy === 'hybrid' && cfg.sourceMode !== 'custom') {
          douyu.send.lastResult = '当前无固定候选，等待爆发或下一周期';
          douyu.send.inFlight = false;
          scheduleSend();
          douyu.dirty = true;
          render();
          return;
        }
        stopSending('没有可发送的聚合弹幕');
        return;
      }
      let index = 0;
      if (!burstCandidate) {
        index = cfg.sourceMode === 'random'
          ? Math.floor(Math.random() * candidates.length)
          : douyu.send.cursor % candidates.length;
        douyu.send.cursor += 1;
      }
      const selectedText = burstCandidate ? burstCandidate.text : candidates[index];
      if (isBlacklistedText(selectedText)) {
        douyu.send.inFlight = false;
        douyu.send.lastResult = '候选命中黑名单，已跳过';
        if (!manual && douyu.send.running) scheduleSend();
        render();
        return;
      }
      const text = buildSendMessage(selectedText, cfg);
      if (!text) {
        stopSending('组合后的弹幕为空');
        return;
      }
      if (text.length > cfg.maxLength) {
        stopSending(`弹幕长度超过 ${cfg.maxLength} 字符`);
        return;
      }
      const result = triggerDouyuSend(text);
      if (!result.ok) {
        stopSending(result.reason);
        return;
      }
      await new Promise((resolve) => setTimeout(resolve, 700));
      const current = result.input.tagName === 'TEXTAREA' ? result.input.value : result.input.innerText;
      if (String(current || '').trim() === text.trim()) {
        stopSending('发送后输入框未清空，可能发送失败');
        return;
      }
      douyu.send.lastResult = burstCandidate ? `爆发发送：${text}` : `已发送：${text}`;
      douyu.send.inFlight = false;
      douyu.send.sentCount += 1;
      douyu.send.lastText = text;
      douyu.send.lastSentAt = Date.now();
      douyu.dirty = true;
      if (!manual && douyu.send.running) scheduleSend();
      render();
    }

    function scheduleSend() {
      clearTimeout(douyu.send.timer);
      const cfg = douyu.config.send;
      const min = Math.max(1000, Number(cfg.minIntervalMs) || 10000);
      const max = Math.max(min, Number(cfg.maxIntervalMs) || 20000);
      const delay = randomSendDelay(min, max);
      douyu.send.lastDelayMs = delay;
      douyu.send.nextAt = Date.now() + delay;
      douyu.send.timer = setTimeout(() => {
        douyu.send.timer = null;
        if (!douyu.send.running) return;
        if (douyu.send.inFlight) scheduleSend();
        else sendOnce();
      }, delay);
    }

    function startSending() {
      if (douyu.send.running) return;
      const candidates = getSendCandidates();
      const canWaitForBurst = douyu.config.send.strategy === 'hybrid' && douyu.config.send.sourceMode !== 'custom';
      if (!candidates.length && !canWaitForBurst) {
        douyu.send.lastResult = '没有可发送的聚合弹幕';
        render();
        return;
      }
      douyu.send.running = true;
      douyu.send.sentCount = 0;
      douyu.send.cursor = 0;
      douyu.send.lastResult = '已启动，等待首次发送';
      douyu.dirty = true;
      scheduleSend();
      startBurstMonitor();
      render();
    }

    function stopSending(reason) {
      stopBurstMonitor();
      clearTimeout(douyu.send.timer);
      douyu.send.timer = null;
      douyu.send.running = false;
      douyu.send.inFlight = false;
      douyu.send.lastDelayMs = 0;
      douyu.send.lastSentAt = 0;
      douyu.send.nextAt = 0;
      if (reason) douyu.send.lastResult = reason;
      douyu.dirty = true;
      render();
    }

    function sendManualOnce() {
      if (douyu.send.running) {
        douyu.send.lastResult = '发送进行中，请先停止';
        douyu.dirty = true;
        render();
        return;
      }
      sendOnce({ manual: true });
    }

      const host = document.createElement('div');
      host.id = 'dbp-douyu-host';
      host.style.cssText = 'position:fixed;right:16px;bottom:16px;z-index:2147483647;';
      const shadow = host.attachShadow({ mode: 'open' });
      shadow.innerHTML = `
        <style>
          :host { all: initial; }
          [hidden] { display: none !important; }
          .panel { width: 420px; max-height: 92vh; overflow: auto; box-sizing: border-box; padding: 12px; border: 1px solid #3f4652; border-radius: 8px; background: #171a21; color: #e8edf5; font: 12px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; box-shadow: 0 10px 30px rgba(0,0,0,0.35); }
          .title { display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px; font-size: 14px; font-weight: 700; cursor: move; user-select: none; }
          .title-actions { display: inline-flex; align-items: center; gap: 6px; }
          .minimize-button { display: inline-flex; align-items: center; justify-content: center; width: 24px; height: 22px; padding: 0; border: 0; background: transparent; color: #c9d3e0; }
          .minimize-button:hover { background: #323946; color: #fff; }
          .launcher { display: inline-flex; align-items: center; justify-content: center; width: 42px; height: 42px; padding: 0; border: 1px solid #4b5563; border-radius: 8px; background: #171a21; color: #e8edf5; box-shadow: 0 6px 18px rgba(0,0,0,0.35); }
          .launcher:hover { background: #262b34; color: #fff; }
          .launcher svg, .minimize-button svg { display: block; pointer-events: none; }
          .muted { color: #9da7b5; font-weight: 400; }
          .row { display: flex; align-items: center; gap: 8px; margin-bottom: 8px; }
          .row label { color: #c9d3e0; white-space: nowrap; }
          input[type="range"] { flex: 1; min-width: 90px; }
          input[type="number"], input[type="text"], select, textarea { box-sizing: border-box; padding: 4px 6px; border: 1px solid #4b5563; border-radius: 6px; background: #0f1116; color: #eef2f7; }
          textarea { width: 100%; resize: vertical; margin-bottom: 8px; }
          .blacklist-field { align-items: flex-start; }
          .blacklist-field textarea { flex: 1; width: auto; min-height: 34px; margin-bottom: 0; }
          input[type="number"] { width: 68px; }
          #sendMinMs, #sendMaxMs { width: 88px; }
          button { padding: 5px 9px; border: 1px solid #4b5563; border-radius: 6px; background: #262b34; color: #eef2f7; cursor: pointer; }
          button:hover { background: #323946; }
          .stats { display: grid; grid-template-columns: 1fr 1fr; gap: 4px 10px; margin-bottom: 8px; }
          .stat { color: #c9d3e0; } .stat b { color: #fff; }
          .rooms { max-height: 54px; overflow: auto; margin-bottom: 8px; color: #a7d7a0; }
          .list { max-height: 250px; overflow: auto; padding-right: 2px; }
          .item { display: grid; grid-template-columns: 28px 1fr 52px; gap: 6px; align-items: center; margin-bottom: 5px; }
          .rank { color: #9da7b5; text-align: right; }
          .bar-wrap { position: relative; height: 18px; border-radius: 4px; background: #0f1116; overflow: hidden; }
          .bar { position: absolute; inset: 0 auto 0 0; width: 0; background: #2f6f9f; }
          .bar-text { position: relative; z-index: 1; padding-left: 5px; color: #f3f7fb; }
          .count { color: #a7d7a0; text-align: right; }
          .empty { padding: 12px 0; color: #9da7b5; text-align: center; }
          .status { margin-top: 8px; color: #f0c674; }
          .send-box { margin-top: 8px; padding-top: 8px; border-top: 1px solid #3f4652; }
          .send-box summary { margin-bottom: 8px; cursor: pointer; font-weight: 700; }
          .send-status { margin-top: 6px; color: #a7d7a0; }
          .debug-box { margin-top: 8px; padding-top: 8px; border-top: 1px solid #3f4652; }
          .debug-box summary { margin-bottom: 8px; cursor: pointer; font-weight: 700; }
          .debug-summary { margin-bottom: 6px; color: #c9d3e0; }
          .debug-top { margin-bottom: 6px; padding: 5px 6px; border-radius: 6px; background: #0f1116; color: #f0c674; line-height: 1.5; }
          .debug-list { max-height: 240px; overflow: auto; padding-right: 2px; }
          .debug-item { padding: 5px 0; border-bottom: 1px solid #2c323c; }
          .debug-text { color: #eef2f7; font-weight: 600; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
          .debug-metrics, .debug-state { margin-top: 2px; color: #9da7b5; font-size: 10px; line-height: 1.4; }
          .debug-ok { color: #a7d7a0; } .debug-bad { color: #d68c8c; }
        </style>
        <div class="panel" id="mainPanel">
          <div class="title"><span>斗鱼弹幕聚合 v1.0.0</span><span class="title-actions"><span class="muted" id="roomCount">0 个来源</span><button class="minimize-button" id="minimizeButton" type="button" title="最小化" aria-label="最小化"><svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><path d="M5 12h14"></path></svg></button></span></div>
          <div class="row"><label>滑窗</label><input id="window" type="range" min="1" max="120" step="1" value="10"><input id="windowValue" type="number" min="1" max="120" step="1" value="10"><span>秒</span></div>
          <div class="row"><label>聚类</label><select id="clusterMode"><option value="exact">精确文本</option><option value="simple">循环 + 有序重合</option></select><input id="similarity" type="range" min="0" max="100" step="1" value="80"><span id="similarityLabel">80%</span></div>
          <div class="stats"><div class="stat">窗口内 <b id="windowCount">0</b> 条</div><div class="stat">聚类数 <b id="uniqueCount">0</b></div><div class="stat">镜像总量 <b id="totalCount">0</b></div><div class="stat">来源房间 <b id="activeCount">0</b></div></div>
          <div class="rooms" id="rooms">等待 B 站采样页...</div>
          <div class="list" id="list"><div class="empty">等待弹幕...</div></div>
          <div class="status" id="status">正在读取共享状态...</div>
          <div class="row" style="margin:8px 0 0"><button id="copy" style="flex:1">复制聚合指标</button><button id="clear" style="flex:1">清空镜像</button></div>
          <details class="send-box" id="sendBox">
            <summary>弹幕发送</summary>
            <div class="row"><label>来源</label><select id="sendSource"><option value="top1">聚合 Top1</option><option value="rotate">TopN 轮换</option><option value="random">TopN 随机</option><option value="custom">自定义列表</option></select><span id="sendTopNWrap" style="display:none;align-items:center;gap:4px"><label>数量</label><input id="sendTopN" type="number" min="1" max="50" step="1" value="5" title="TopN 轮换/随机时参与的数量"></span></div>
            <div class="row"><label>策略</label><select id="sendStrategy"><option value="fixed">固定周期</option><option value="hybrid">固定周期 + 爆发提前</option></select></div>
            <div class="row"><label>间隔</label><input id="sendMinMs" type="number" min="1000" step="500" value="10000"><span>~</span><input id="sendMaxMs" type="number" min="1000" step="500" value="20000"><span>ms</span></div>
            <div id="sendBurstWrap" style="display:none">
              <div class="row"><label>爆发</label><input id="sendBurstRecent" type="number" min="1" max="30" step="1" value="3" title="最近检测秒数"><span>秒 /</span><input id="sendBurstBaseline" type="number" min="10" max="120" step="5" value="30" title="基线秒数"><span>秒基线</span></div>
              <div class="row"><label>触发</label><input id="sendBurstMinCount" type="number" min="1" max="100" step="1" value="4" title="最近窗口最少弹幕数"><span>条 /</span><input id="sendBurstLift" type="number" min="1" max="20" step="0.1" value="2.5" title="相对基线放大倍数"><span>倍 /</span><input id="sendBurstShare" type="number" min="0" max="100" step="1" value="10" title="占比增量百分比"><span>%</span></div>
              <div class="row"><label>确认</label><input id="sendBurstConfirm" type="number" min="1" max="10" step="1" value="2" title="连续满足次数"><span>次 /</span><input id="sendBurstCooldown" type="number" min="0" max="300" step="1" value="15" title="发送后冷却秒数"><span>秒冷却</span></div>
            </div>
            <div class="row"><label>前缀</label><input id="sendPrefix" type="text" style="flex:1" placeholder="可选"></div>
            <div class="row"><label>后缀</label><input id="sendSuffix" type="text" style="flex:1" placeholder="可选"></div>
            <div class="row blacklist-field"><label>黑名单</label><textarea id="sendBlacklist" rows="2" placeholder="纯文本全匹配；正则可直接写或使用 /表达式/flags" title="纯文本按整条弹幕全匹配；包含正则语法时按正则表达式处理"></textarea></div>
            <div class="row"><button id="sendStart" style="flex:1">开始发送</button><button id="sendOnce" style="flex:1">发送一次</button></div>
            <textarea id="sendCustom" rows="3" placeholder="自定义列表，一行一条" style="display:none"></textarea>
            <div class="send-status" id="sendStatus">未启动</div>
          </details>
          <details class="debug-box" id="debugBox" open>
            <summary>爆发热点检测调试</summary>
            <div class="row"><button id="debugStart" style="flex:1">模拟启动</button><span id="debugStatus" class="muted">未启动</span></div>
            <div class="debug-summary" id="debugSummary"></div>
            <div class="debug-top" id="debugTop">暂无候选</div>
            <div class="debug-list" id="debugList"><div class="empty">模拟启动后显示候选数据。</div></div>
          </details>
        </div>
        <button class="launcher" id="launcher" type="button" title="展开斗鱼弹幕聚合" aria-label="展开斗鱼弹幕聚合" hidden>
          <svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="5" width="18" height="14" rx="2"></rect><path d="M7 15h3M13 15h4"></path></svg>
        </button>
      `;
      document.documentElement.appendChild(host);
      const refs = { roomCount: shadow.getElementById('roomCount'), window: shadow.getElementById('window'), windowValue: shadow.getElementById('windowValue'), clusterMode: shadow.getElementById('clusterMode'), similarity: shadow.getElementById('similarity'), similarityLabel: shadow.getElementById('similarityLabel'), windowCount: shadow.getElementById('windowCount'), uniqueCount: shadow.getElementById('uniqueCount'), totalCount: shadow.getElementById('totalCount'), activeCount: shadow.getElementById('activeCount'), rooms: shadow.getElementById('rooms'), list: shadow.getElementById('list'), status: shadow.getElementById('status'), copy: shadow.getElementById('copy'), clear: shadow.getElementById('clear') };
      refs.panel = shadow.getElementById('mainPanel');
      refs.minimizeButton = shadow.getElementById('minimizeButton');
      refs.launcher = shadow.getElementById('launcher');
      refs.sendBox = shadow.getElementById('sendBox');
      refs.sendSource = shadow.getElementById('sendSource');
      refs.sendTopN = shadow.getElementById('sendTopN');
      refs.sendTopNWrap = shadow.getElementById('sendTopNWrap');
      refs.sendStrategy = shadow.getElementById('sendStrategy');
      refs.sendBurstWrap = shadow.getElementById('sendBurstWrap');
      refs.sendBurstRecent = shadow.getElementById('sendBurstRecent');
      refs.sendBurstBaseline = shadow.getElementById('sendBurstBaseline');
      refs.sendBurstMinCount = shadow.getElementById('sendBurstMinCount');
      refs.sendBurstLift = shadow.getElementById('sendBurstLift');
      refs.sendBurstShare = shadow.getElementById('sendBurstShare');
      refs.sendBurstConfirm = shadow.getElementById('sendBurstConfirm');
      refs.sendBurstCooldown = shadow.getElementById('sendBurstCooldown');
      refs.sendMinMs = shadow.getElementById('sendMinMs');
      refs.sendMaxMs = shadow.getElementById('sendMaxMs');
      refs.sendPrefix = shadow.getElementById('sendPrefix');
      refs.sendSuffix = shadow.getElementById('sendSuffix');
      refs.sendBlacklist = shadow.getElementById('sendBlacklist');
      refs.sendStart = shadow.getElementById('sendStart');
      refs.sendOnce = shadow.getElementById('sendOnce');
      refs.sendCustom = shadow.getElementById('sendCustom');
      refs.sendStatus = shadow.getElementById('sendStatus');
      refs.debugStart = shadow.getElementById('debugStart');
      refs.debugStatus = shadow.getElementById('debugStatus');
      refs.debugSummary = shadow.getElementById('debugSummary');
      refs.debugTop = shadow.getElementById('debugTop');
      refs.debugList = shadow.getElementById('debugList');
      douyu.refs = refs;
      const UI_STORAGE_KEY = 'dbp:douyu:ui:v1';
      const LAUNCHER_SIZE = 42;
      function readUiState() {
        try {
          const saved = JSON.parse(localStorage.getItem(UI_STORAGE_KEY) || 'null');
          if (!saved || typeof saved !== 'object') return;
          douyu.ui.minimized = !!saved.minimized;
          ['panelLeft', 'panelTop', 'launcherLeft', 'launcherTop'].forEach((key) => {
            const value = Number(saved[key]);
            if (Number.isFinite(value)) douyu.ui[key] = value;
          });
        } catch (error) { /* ignore invalid UI state */ }
      }
      function saveUiState() {
        try {
          localStorage.setItem(UI_STORAGE_KEY, JSON.stringify({
            minimized: douyu.ui.minimized,
            panelLeft: douyu.ui.panelLeft,
            panelTop: douyu.ui.panelTop,
            launcherLeft: douyu.ui.launcherLeft,
            launcherTop: douyu.ui.launcherTop,
          }));
        } catch (error) { /* ignore storage failures */ }
      }
      function setHostPosition(left, top, fallbackWidth, fallbackHeight) {
        const width = Math.max(1, host.offsetWidth || fallbackWidth || 1);
        const height = Math.max(1, host.offsetHeight || fallbackHeight || 1);
        const maxLeft = Math.max(0, window.innerWidth - width);
        const maxTop = Math.max(0, window.innerHeight - height);
        const nextLeft = Math.min(maxLeft, Math.max(0, Number.isFinite(Number(left)) ? Number(left) : 0));
        const nextTop = Math.min(maxTop, Math.max(0, Number.isFinite(Number(top)) ? Number(top) : 0));
        host.style.left = `${nextLeft}px`;
        host.style.top = `${nextTop}px`;
        host.style.right = 'auto';
        host.style.bottom = 'auto';
      }
      function isPlayerImmersive() {
        const fullscreenElement = document.fullscreenElement || document.webkitFullscreenElement || document.msFullscreenElement;
        if (fullscreenElement) return true;
        const viewportWidth = Math.max(1, window.innerWidth);
        const viewportHeight = Math.max(1, window.innerHeight);
        const rects = [];
        document.querySelectorAll('video').forEach((video) => {
          const videoRect = video.getBoundingClientRect();
          if (videoRect.width >= 160 && videoRect.height >= 90) rects.push(videoRect);
          const container = video.closest('.room-Player-Box, .layout-Player, .layout-Player-videoEntity, [class*="playerWrap"], [class*="Player"]');
          if (container) rects.push(container.getBoundingClientRect());
        });
        return rects.some((rect) => {
          const widthRatio = rect.width / viewportWidth;
          const heightRatio = rect.height / viewportHeight;
          const areaRatio = widthRatio * heightRatio;
          const visible = rect.bottom > 0 && rect.right > 0 && rect.top < viewportHeight && rect.left < viewportWidth;
          return visible && widthRatio >= 0.9 && heightRatio >= 0.78 && areaRatio >= 0.72 && rect.top <= 12 && rect.left <= 12;
        });
      }
      function syncImmersiveVisibility() {
        const immersive = isPlayerImmersive();
        douyu.ui.immersive = immersive;
        refs.panel.hidden = douyu.ui.minimized;
        refs.launcher.hidden = !douyu.ui.minimized || immersive;
      }
      function syncPanelUi() {
        if (douyu.ui.minimized) {
          refs.panel.hidden = true;
          refs.launcher.hidden = false;
          setHostPosition(douyu.ui.launcherLeft, douyu.ui.launcherTop, LAUNCHER_SIZE, LAUNCHER_SIZE);
        } else {
          refs.launcher.hidden = true;
          refs.panel.hidden = false;
          setHostPosition(douyu.ui.panelLeft, douyu.ui.panelTop, 420, 420);
        }
        syncImmersiveVisibility();
      }
      function captureCurrentHostPosition() {
        const rect = host.getBoundingClientRect();
        if (douyu.ui.minimized) {
          douyu.ui.launcherLeft = rect.left;
          douyu.ui.launcherTop = rect.top;
        } else {
          douyu.ui.panelLeft = rect.left;
          douyu.ui.panelTop = rect.top;
        }
      }
      function recordCurrentHostPosition() {
        captureCurrentHostPosition();
        saveUiState();
      }
      function showPanel() {
        if (!douyu.ui.minimized) return;
        douyu.ui.minimized = false;
        refs.launcher.hidden = true;
        refs.panel.hidden = false;
        setHostPosition(douyu.ui.panelLeft, douyu.ui.panelTop, 420, 420);
        syncImmersiveVisibility();
        saveUiState();
      }
      function minimizePanel() {
        if (douyu.ui.minimized) return;
        const rect = host.getBoundingClientRect();
        douyu.ui.panelLeft = rect.left;
        douyu.ui.panelTop = rect.top;
        if (!Number.isFinite(douyu.ui.launcherLeft)) douyu.ui.launcherLeft = rect.right - LAUNCHER_SIZE;
        if (!Number.isFinite(douyu.ui.launcherTop)) douyu.ui.launcherTop = rect.top;
        douyu.ui.minimized = true;
        douyu.sendUiEditing = false;
        refs.panel.hidden = true;
        refs.launcher.hidden = false;
        setHostPosition(douyu.ui.launcherLeft, douyu.ui.launcherTop, LAUNCHER_SIZE, LAUNCHER_SIZE);
        syncImmersiveVisibility();
        saveUiState();
      }
      function handleViewportChange() {
        if (douyu.ui.minimized) setHostPosition(douyu.ui.launcherLeft, douyu.ui.launcherTop, LAUNCHER_SIZE, LAUNCHER_SIZE);
        else setHostPosition(douyu.ui.panelLeft, douyu.ui.panelTop, 420, 420);
        captureCurrentHostPosition();
        syncImmersiveVisibility();
        saveUiState();
      }
      readUiState();
      const initialRect = host.getBoundingClientRect();
      if (!Number.isFinite(douyu.ui.panelLeft) || !Number.isFinite(douyu.ui.panelTop)) {
        douyu.ui.panelLeft = initialRect.left;
        douyu.ui.panelTop = initialRect.top;
      }
      if (!Number.isFinite(douyu.ui.launcherLeft) || !Number.isFinite(douyu.ui.launcherTop)) {
        douyu.ui.launcherLeft = initialRect.right - LAUNCHER_SIZE;
        douyu.ui.launcherTop = initialRect.top;
      }
      makeDraggablePanel(host, shadow.querySelector('.title'), { onDrop: recordCurrentHostPosition });
      makeDraggablePanel(host, refs.launcher, { allowInteractiveHandle: true, dragThreshold: 5, onClick: showPanel, onDrop: recordCurrentHostPosition });
      refs.minimizeButton.addEventListener('click', minimizePanel);
      refs.launcher.addEventListener('keydown', (event) => {
        if (event.key !== 'Enter' && event.key !== ' ') return;
        event.preventDefault();
        showPanel();
      });
      window.addEventListener('resize', handleViewportChange);
      document.addEventListener('fullscreenchange', syncImmersiveVisibility);
      document.addEventListener('webkitfullscreenchange', syncImmersiveVisibility);
      document.addEventListener('msfullscreenchange', syncImmersiveVisibility);
      douyu.syncImmersiveVisibility = syncImmersiveVisibility;
      syncPanelUi();
      saveUiState();
      refs.sendBox.addEventListener('focusin', () => { douyu.sendUiEditing = true; });
      refs.sendBox.addEventListener('focusout', () => {
        setTimeout(() => {
          if (sendBoxContainsActiveElement()) return;
          douyu.sendUiEditing = false;
          syncSendUI();
        }, 0);
      });
      syncSendUI();
      function updateSendConfigFromUI() {
        const previousStrategy = douyu.config.send.strategy;
        const previousSource = douyu.config.send.sourceMode;
        const previousMin = douyu.config.send.minIntervalMs;
        const previousMax = douyu.config.send.maxIntervalMs;
        writeConfig({
          send: {
            ...douyu.config.send,
            strategy: refs.sendStrategy.value,
            sourceMode: refs.sendSource.value,
            topN: Number(refs.sendTopN.value) || 5,
            minIntervalMs: Number(refs.sendMinMs.value) || 10000,
            maxIntervalMs: Number(refs.sendMaxMs.value) || 20000,
            burst: {
              ...douyu.config.send.burst,
              recentSec: Number(refs.sendBurstRecent.value) || 3,
              baselineSec: Number(refs.sendBurstBaseline.value) || 30,
              minCount: Number(refs.sendBurstMinCount.value) || 4,
              minLift: Number(refs.sendBurstLift.value) || 2.5,
              minShareDelta: Number(refs.sendBurstShare.value) / 100,
              confirmCount: Number(refs.sendBurstConfirm.value) || 2,
              cooldownSec: Number(refs.sendBurstCooldown.value) || 15,
            },
            prefix: refs.sendPrefix.value,
            suffix: refs.sendSuffix.value,
            customText: refs.sendCustom.value,
            blacklist: refs.sendBlacklist.value,
          },
        });
        refs.sendCustom.style.display = refs.sendSource.value === 'custom' ? 'block' : 'none';
        refs.sendTopNWrap.style.display = ['rotate', 'random'].includes(refs.sendSource.value) ? 'inline-flex' : 'none';
        refs.sendBurstWrap.style.display = refs.sendStrategy.value === 'hybrid' && refs.sendSource.value !== 'custom' ? 'block' : 'none';
        const strategyChanged = previousStrategy !== douyu.config.send.strategy;
        const sourceChanged = previousSource !== douyu.config.send.sourceMode;
        if (douyu.send.running && (strategyChanged || sourceChanged)) {
          if (douyu.config.send.strategy === 'hybrid' && douyu.config.send.sourceMode !== 'custom') startBurstMonitor();
          else stopBurstMonitor();
        }
        if (douyu.send.running && (previousMin !== douyu.config.send.minIntervalMs || previousMax !== douyu.config.send.maxIntervalMs)) scheduleSend();
        render();
      }
      refs.sendSource.addEventListener('change', updateSendConfigFromUI);
      refs.sendStrategy.addEventListener('change', updateSendConfigFromUI);
      [refs.sendTopN, refs.sendMinMs, refs.sendMaxMs, refs.sendPrefix, refs.sendSuffix, refs.sendBlacklist, refs.sendCustom, refs.sendBurstRecent, refs.sendBurstBaseline, refs.sendBurstMinCount, refs.sendBurstLift, refs.sendBurstShare, refs.sendBurstConfirm, refs.sendBurstCooldown].forEach((el) => el.addEventListener('input', updateSendConfigFromUI));
      refs.sendStart.addEventListener('click', () => {
        if (douyu.send.running) stopSending('手动停止');
        else startSending();
      });
      refs.sendOnce.addEventListener('click', sendManualOnce);
      refs.debugStart.addEventListener('click', () => {
        if (douyu.debug.running) stopDebugSimulation();
        else startDebugSimulation();
        render();
      });
      refs.window.value = String(douyu.config.windowSec);
      refs.windowValue.value = String(douyu.config.windowSec);
      refs.clusterMode.value = douyu.config.clusterMode;
      refs.similarity.value = String(Math.round(douyu.config.similarity * 100));
      refs.similarityLabel.textContent = `${refs.similarity.value}%`;
      refs.similarity.disabled = douyu.config.clusterMode !== 'simple';
      function setWindow(value) {
        const next = Math.max(1, Math.min(BRIDGE_MAX_WINDOW_SEC, Number(value) || 1));
        refs.window.value = String(next); refs.windowValue.value = String(next);
        writeConfig({ windowSec: next }); render();
      }
      refs.window.addEventListener('input', () => setWindow(refs.window.value));
      refs.windowValue.addEventListener('change', () => setWindow(refs.windowValue.value));
      refs.clusterMode.addEventListener('change', () => {
        refs.similarity.disabled = refs.clusterMode.value !== 'simple';
        writeConfig({ clusterMode: refs.clusterMode.value });
        render();
      });
      refs.similarity.addEventListener('input', () => { refs.similarityLabel.textContent = `${refs.similarity.value}%`; writeConfig({ similarity: Number(refs.similarity.value) / 100 }); render(); });
      refs.clear.addEventListener('click', () => {
        GM_setValue(STORAGE.rooms, []);
        douyu.rooms.clear();
        douyu.dataRevision += 1;
        douyu.aggregateCache = null;
        douyu.clusterBaseCache = null;
        douyu.dirty = true;
        refs.status.textContent = '已清空本地镜像和来源列表。';
        render();
      });
      refs.copy.addEventListener('click', async () => {
        const result = aggregate();
        const payload = { url: location.href, exportedAt: Date.now(), config: douyu.config, rooms: [...douyu.rooms.values()].map((room) => ({ roomId: room.roomId, lastSeen: room.lastSeen, lastSeq: room.lastSeq, bufferCount: room.events.length, windowCount: result.perRoom.get(room.roomId) || 0 })), windowCount: result.records.length, uniqueCount: result.clusters.length, top: result.clusters.slice(0, 50) };
        const text = JSON.stringify(payload, null, 2);
        try { await navigator.clipboard.writeText(text); refs.status.textContent = '聚合指标已复制到剪贴板。'; } catch (error) { window.prompt('复制下面的聚合指标：', text); }
      });
      return refs;
    }
    function updateSendStatus() {
      if (!douyu.refs || !douyu.refs.sendStart || !douyu.refs.sendStatus) return;
      douyu.refs.sendStart.textContent = douyu.send.running ? '停止发送' : '开始发送';
      if (!douyu.send.running) {
        douyu.refs.sendStatus.textContent = douyu.send.lastResult || '未启动';
        return;
      }
      const remainingMs = douyu.send.nextAt ? douyu.send.nextAt - Date.now() : 0;
      const nextText = remainingMs > 0 ? `下次约 ${Math.ceil(remainingMs / 1000)} 秒后` : '即将发送（后台标签页可能被节流）';
      const delayText = douyu.send.lastDelayMs ? `本次间隔 ${douyu.send.lastDelayMs}ms` : '';
      const strategyText = douyu.config.send.strategy === 'hybrid' ? '固定+爆发(可打断)' : '固定周期';
      const burstText = douyu.config.send.strategy === 'hybrid' && douyu.burst.status ? `；${douyu.burst.status}` : '';
      douyu.refs.sendStatus.textContent = `发送中（${strategyText}）：已发 ${douyu.send.sentCount} 条，${delayText}，${nextText}${burstText}。${douyu.send.lastResult || ''}`;
    }

    function render(force = false) {
      if (!douyu.refs) return;
      if (!douyu.dirty && !force) {
        updateSendStatus();
        douyu.updateDebugPanel?.();
        return;
      }
      douyu.dirty = false;
      const result = aggregate();
      const activeRooms = [...douyu.rooms.values()].filter((room) => Date.now() - room.lastSeen <= 5000);
      const totalEvents = [...douyu.rooms.values()].reduce((sum, room) => sum + room.events.length, 0);
      douyu.refs.roomCount.textContent = `${activeRooms.length} 个来源`;
      douyu.refs.windowCount.textContent = String(result.records.length);
      douyu.refs.uniqueCount.textContent = String(result.clusters.length);
      douyu.refs.totalCount.textContent = String(totalEvents);
      douyu.refs.activeCount.textContent = String(activeRooms.length);
      douyu.refs.rooms.textContent = douyu.rooms.size ? [...douyu.rooms.values()].map((room) => `#${room.roomId} ${Date.now() - room.lastSeen <= 5000 ? '活跃' : '离线'} ${result.perRoom.get(room.roomId) || 0}条`).join('  |  ') : '等待 B 站采样页...';
      if (!result.clusters.length) douyu.refs.list.innerHTML = '<div class="empty">等待弹幕...</div>';
      else {
        const top = result.clusters.slice(0, 20);
        const maxCount = top[0].count;
        const rows = top.map((item, index) => { const row = document.createElement('div'); row.className = 'item'; const rank = document.createElement('div'); rank.className = 'rank'; rank.textContent = String(index + 1); const barWrap = document.createElement('div'); barWrap.className = 'bar-wrap'; const bar = document.createElement('div'); bar.className = 'bar'; bar.style.width = `${Math.max(4, (item.count / maxCount) * 100)}%`; const barText = document.createElement('div'); barText.className = 'bar-text'; barText.textContent = item.text; barWrap.append(bar, barText); const count = document.createElement('div'); count.className = 'count'; count.textContent = String(item.count); row.append(rank, barWrap, count); return row; });
        douyu.refs.list.replaceChildren(...rows);
      }
      const modeNote = douyu.config.clusterMode === 'simple' ? ` 循环+有序重合，阈值 ${Math.round(douyu.config.similarity * 100)}%。` : '';
      const version = typeof GM_info !== 'undefined' && GM_info.script ? GM_info.script.version : '?';
      const knownRoomCount = roomList().length;
      const diag = `脚本 v${version}，登记 ${knownRoomCount} 个房间`;
      douyu.refs.status.textContent = activeRooms.length
        ? `聚合中，滑窗 ${douyu.config.windowSec} 秒（${diag}）。${modeNote}`
        : `等待 B 站采样页（${diag}）。${modeNote}`;
      updateSendStatus();
      douyu.updateDebugPanel?.();
    }
    douyu.refs = createDouyuPanel();
    try {
      douyu.listeners.push(addValueChangeListener(STORAGE.rooms, () => { refreshRegistry(); render(); }));
    douyu.listeners.push(addValueChangeListener(STORAGE.config, (_name, _oldValue, newValue) => { douyu.config = normalizeBridgeConfig(newValue); douyu.syncSendUI?.(); douyu.dirty = true; render(); }));
      refreshRegistry();
      douyu.pollTimer = setInterval(() => { refreshRegistry(); render(true); douyu.syncImmersiveVisibility?.(); }, 1000);
      douyu.renderTimer = setInterval(render, BRIDGE_RENDER_MS);
      render();
    } catch (error) {
      console.error('[DBP Bridge] init failed:', error);
      if (douyu.refs && douyu.refs.status) {
        douyu.refs.status.textContent = `初始化失败：${error && error.message ? error.message : String(error)}`;
      }
    }
  }
})();
