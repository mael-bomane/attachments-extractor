// ==UserScript==
// @name         Discord Attachment Collector
// @namespace    https://tampermonkey.net/
// @version      1.4.0
// @description  Collect attachment URLs from a specific user in a Discord channel and export to .txt
// @author       You
// @match        https://discord.com/*
// @grant        none
// @run-at       document-idle
// ==/UserScript==

(function () {
  "use strict";

  // ─────────────────────────────────────────────────────────────────────────
  // CONFIGURATION
  // ─────────────────────────────────────────────────────────────────────────
  const CFG = {
    mutationTimeout: 1400, // max ms to wait for Discord to load new messages
    mutationSettle:  180,  // ms after a DOM mutation fires before we scan
    maxNoNew:        5,    // consecutive scrolls with zero new messages → stop
  };

  // ── Scroll speed — persisted in localStorage ────────────────────────────
  const SCROLL_DELAY_KEY     = "dac-scroll-delay";
  const SCROLL_DELAY_DEFAULT = 500;  // ms
  const SCROLL_DELAY_MIN     = 100;
  const SCROLL_DELAY_MAX     = 2000;

  // Initialise from localStorage so the last-used speed survives page reloads.
  // Wrapped in try/catch: a SecurityError here (storage blocked, incognito,
  // sandboxed iframe) would otherwise crash the entire script before init()
  // runs and prevent the toggle button from ever appearing.
  let scrollDelay = (() => {
    try {
      const saved = parseInt(localStorage.getItem(SCROLL_DELAY_KEY));
      return (saved >= SCROLL_DELAY_MIN && saved <= SCROLL_DELAY_MAX)
        ? saved
        : SCROLL_DELAY_DEFAULT;
    } catch {
      return SCROLL_DELAY_DEFAULT;
    }
  })();

  // ─────────────────────────────────────────────────────────────────────────
  // DOM SELECTORS
  // Discord uses hashed class names that change on deploy.
  // We rely on partial class matching and stable data-* attributes instead.
  // ─────────────────────────────────────────────────────────────────────────
  const SEL = {
    appMount:    "#app-mount",
    messagesOL:  'ol[data-list-id="chat-messages"]',
    messageItem: 'li[id^="chat-messages-"]',
    // Elements that carry data-user-id (avatar container, username button, etc.)
    dataUserId:  '[data-user-id]',
    // All anchor tags linking to either Discord CDN host
    linkCdn:     'a[href*="cdn.discordapp.com"]',
    linkMedia:   'a[href*="media.discordapp.net"]',
    // Every <img> inside a message (we filter noise afterward)
    anyImg:      "img[src]",
    // Video elements and their <source> children
    anyVideo:    "video[src], video source[src]",
  };

  // ─────────────────────────────────────────────────────────────────────────
  // URL HELPERS
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Produce a stable deduplication key from a raw URL.
   * Strips the query-string and fragment so the same attachment URL with
   * different expiry/format params (ex=, is=, hm=, format=, quality=) always
   * maps to the same key. The hostname is intentionally left unchanged so
   * that media.discordapp.net stays as media.discordapp.net in the key
   * (and therefore in the exported output).
   */
  function normalizeUrl(raw) {
    try {
      const u = new URL(raw);
      return u.origin + u.pathname; // query-stripped, host unchanged
    } catch {
      return raw.split("?")[0].split("#")[0];
    }
  }

  /**
   * Path segments that identify non-content Discord assets.
   * Any URL whose pathname contains one of these is treated as UI noise
   * (emoji, avatar, server icon, banner, role icon, sticker).
   */
  const NOISE_PATHS = [
    "/emojis/",
    "/avatars/",
    "/icons/",
    "/banners/",
    "/splashes/",
    "/role-icons/",
    "/stickers/",
    "/channel-icons/",
    "/embed/avatars/",
  ];

  /**
   * The only URL structure we want to collect.
   * Must be a Discord media-proxy attachment URL with an allowed image extension.
   *
   *   https://media.discordapp.net/attachments/<channel>/<attach>/filename.png
   *
   * Allowed extensions: .png  .jpg  .jpeg  .webp
   * Excluded:  avatars, emojis, stickers, embeds, GIFs, Tenor, cdn.discordapp.com, etc.
   */
  const ATTACH_MARKER  = "media.discordapp.net/attachments/";
  const ATTACH_EXT_RE  = /\.(png|jpe?g|webp)(\?|$)/i;

  /** Image file extensions used only for the "image" vs "file" counter label. */
  const IMAGE_EXT_RE = ATTACH_EXT_RE; // everything we collect is an image

  /**
   * Returns true if a URL or its source element looks like UI noise
   * (emoji, avatar, tiny icon) that should be ignored.
   */
  function isNoise(url, el) {
    try {
      const path = new URL(url).pathname;
      if (NOISE_PATHS.some((p) => path.includes(p))) return true;
    } catch {
      /* ignore bad URLs */
    }

    if (!el) return false;

    // Discord marks emoji <img> elements with role="img" aria-label and
    // class names containing "emoji".  Check both.
    if (
      el.closest('[class*="emoji"]') ||
      el.getAttribute("data-type") === "emoji" ||
      (el.getAttribute("aria-label") && el.getAttribute("role") === "img" &&
        (el.naturalWidth <= 24 || parseInt(el.getAttribute("width")) <= 24))
    ) return true;

    // Tiny rendered size is a strong signal for emoji / reaction images.
    const w = el.naturalWidth  || parseInt(el.getAttribute("width")  || "0");
    const h = el.naturalHeight || parseInt(el.getAttribute("height") || "0");
    if (w > 0 && w <= 24 && h > 0 && h <= 24) return true;

    return false;
  }

  /**
   * Returns true only for Discord attachment URLs with an allowed extension.
   * Checked on the raw URL before normalization so the /attachments/ path
   * segment and extension are still present.
   */
  function isAttachmentUrl(url) {
    return url.includes(ATTACH_MARKER) && ATTACH_EXT_RE.test(url);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // RUNTIME STATE
  // ─────────────────────────────────────────────────────────────────────────
  let isRunning       = false;
  let shouldStop      = false;
  let collectedUrls   = new Set();   // deduplicated, normalized media URLs (global dedup)
  let urlsByMessage   = new Map();   // Map<messageId, string[]> — grouped for export
  let processedMsgIds = new Set();   // <li> IDs already scanned
  let messagesScanned = 0;
  let filesFound      = 0;   // non-image attachments (PDFs, ZIPs, videos, …)
  let imagesFound     = 0;   // image URLs (.png, .jpg, .gif, .webp, …)

  // ─────────────────────────────────────────────────────────────────────────
  // UTILITIES
  // ─────────────────────────────────────────────────────────────────────────
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

  /** Extract the channel ID from the current URL path. */
  function getCurrentChannelId() {
    const m = window.location.pathname.match(/\/channels\/\d+\/(\d+)/);
    return m ? m[1] : "";
  }

  /**
   * Walk up the DOM from the messages <ol> to find its scrollable ancestor.
   * We check overflowY and that the element can actually scroll.
   */
  function findScroller() {
    const ol = document.querySelector(SEL.messagesOL);
    if (!ol) return null;

    let el = ol.parentElement;
    while (el && el !== document.body) {
      const style = getComputedStyle(el);
      const overflowY = style.overflowY;
      const canScroll = overflowY === "scroll" || overflowY === "auto";
      if (canScroll && el.scrollHeight > el.clientHeight) return el;
      el = el.parentElement;
    }
    return null;
  }

  /**
   * Attempt to extract the numeric Discord user ID from a message <li>.
   *
   * Discord marks the first message in every cozy group with several
   * attributes that encode the author's ID. We try three sources in order
   * of reliability:
   *
   *   1. data-user-id attribute — Discord attaches this to the avatar
   *      container, the username button, and sometimes the message header
   *      wrapper. It is the most direct source.
   *
   *   2. Profile anchor href — the clickable username/avatar links to
   *      /users/{id} (or a channel-specific path). We extract the snowflake
   *      from that URL with a regex.
   *
   *   3. Avatar image src — CDN avatar URLs embed the owner's ID in the
   *      path: cdn.discordapp.com/avatars/{userId}/{hash}.ext
   *
   * Continuation messages in the same group have none of these elements, so
   * callers must carry the last-seen ID forward (see processVisibleMessages).
   *
   * Returns the user ID string (numeric snowflake) or null.
   */
  function extractAuthorId(liEl) {
    // 1. Direct data attribute — fastest and most reliable.
    const tagged = liEl.querySelector(SEL.dataUserId);
    if (tagged) return tagged.getAttribute("data-user-id");

    // 2. Profile anchor link: href="/users/123..." or "/@me" flows included.
    const anchor = liEl.querySelector('a[href*="/users/"]');
    if (anchor) {
      const m = anchor.href.match(/\/users\/(\d{10,20})/);
      if (m) return m[1];
    }

    // 3. Avatar image src encodes the user ID in the CDN path.
    const avatar = liEl.querySelector('img[src*="/avatars/"]');
    if (avatar) {
      const m = (avatar.src || "").match(/\/avatars\/(\d{10,20})\//);
      if (m) return m[1];
    }

    return null;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // MESSAGE PROCESSING
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Extract all media URLs from a single <li> message element.
   *
   * Sources scanned (in priority order):
   *   1. <img src> — primary source. Discord renders attachment images through
   *      media.discordapp.net and the img.src always carries the full proxy
   *      URL including format/quality params. Processed first so that when
   *      both an <img> and a wrapping <a> point to the same attachment, the
   *      img.src wins and is what gets exported.
   *   2. <a href> links to media.discordapp.net — fallback for cases where
   *      an image has not yet rendered but the anchor is already in the DOM.
   *      cdn.discordapp.com anchor links are excluded by isAttachmentUrl.
   *   3. <video src> / <source src> — video attachments (not currently
   *      matched by isAttachmentUrl's extension check, kept for future use).
   *
   * Returns a Map<deduplicationKey, {type, rawUrl}> where:
   *   - key     = query-stripped URL (media.discordapp.net/attachments/…/file.png)
   *   - rawUrl  = the original URL with all query params — this is what gets exported
   *   - type    = "image" | "file" for the counter display
   */
  function extractMedia(liEl) {
    /** @type {Map<string, {type: "image"|"file", rawUrl: string}>} */
    const found = new Map();

    function add(rawUrl, el) {
      if (!isAttachmentUrl(rawUrl)) return;
      if (isNoise(rawUrl, el))      return;
      const key = normalizeUrl(rawUrl); // query-stripped path used for dedup
      if (!found.has(key)) {
        found.set(key, {
          type:   IMAGE_EXT_RE.test(key) ? "image" : "file",
          rawUrl, // full URL with query params — exported as-is
        });
      }
    }

    // ── 1. Inline images — preferred source (always media.discordapp.net) ──
    liEl.querySelectorAll(SEL.anyImg).forEach((img) => {
      if (!img.src || img.src.startsWith("data:")) return;
      add(img.src, img);
    });

    // ── 2. Anchor links — fallback; cdn.discordapp.com links are filtered ──
    liEl.querySelectorAll(SEL.linkCdn).forEach((a)  => add(a.href, null));
    liEl.querySelectorAll(SEL.linkMedia).forEach((a) => add(a.href, null));

    // ── 3. Video attachments ───────────────────────────────────────────────
    liEl.querySelectorAll(SEL.anyVideo).forEach((el) => {
      const src = el.src || el.getAttribute("src");
      if (src) add(src, null);
    });

    return found;
  }

  /**
   * Scan every currently-visible message <li> in the chat list.
   *
   * Discord groups consecutive messages from the same author into a visual
   * block. Only the first message in a block has author-identifying elements
   * (avatar, username button, data-user-id). We carry `currentAuthorId`
   * forward so continuation messages are attributed to the same person.
   *
   * Media URLs are stored in two places:
   *   - collectedUrls (Set)    — global deduplication across all messages.
   *   - urlsByMessage (Map)    — per-message grouping for the export format.
   *
   * Returns the number of *new* media URLs collected this pass.
   */
  function processVisibleMessages(targetUserId) {
    const ol = document.querySelector(SEL.messagesOL);
    if (!ol) return 0;

    let newFound = 0;
    let currentAuthorId = null;

    ol.querySelectorAll(SEL.messageItem).forEach((li) => {
      const msgId = li.id;

      // Update the tracked author ID when this <li> is a group header.
      const foundId = extractAuthorId(li);
      if (foundId) currentAuthorId = foundId;

      // Record as scanned (only increment total for first-time IDs).
      if (!processedMsgIds.has(msgId)) {
        processedMsgIds.add(msgId);
        messagesScanned++;
      }

      // Skip messages with no identified author or wrong author.
      if (!currentAuthorId) return;
      if (currentAuthorId !== targetUserId) return;

      // Collect new media from this message, grouped by its message ID.
      // key    = query-stripped URL (dedup handle)
      // entry  = { type, rawUrl } where rawUrl keeps all query params
      extractMedia(li).forEach(({ type, rawUrl }, key) => {
        if (collectedUrls.has(key)) return; // already seen in another message
        collectedUrls.add(key);
        if (type === "image") imagesFound++;
        else                  filesFound++;
        newFound++;

        // Store the full raw URL (with format/quality params) for export.
        if (!urlsByMessage.has(msgId)) urlsByMessage.set(msgId, []);
        urlsByMessage.get(msgId).push(rawUrl);
      });
    });

    return newFound;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // SCROLL LOOP
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Scroll to the top of the scroller and wait for Discord to load new
   * messages using a MutationObserver on the messages <ol>.
   *
   * Resolves with the number of new <li> elements added to the DOM.
   * Falls back to resolving after `CFG.mutationTimeout` ms if nothing fires.
   */
  function scrollAndWaitForLoad(scroller) {
    return new Promise((resolve) => {
      const ol = document.querySelector(SEL.messagesOL);
      if (!ol) { resolve(0); return; }

      const before = ol.querySelectorAll(SEL.messageItem).length;
      let settled  = false;

      const finish = () => {
        if (settled) return;
        settled = true;
        obs.disconnect();
        clearTimeout(fallback);
        resolve(ol.querySelectorAll(SEL.messageItem).length - before);
      };

      // Watch for child additions directly inside the <ol>.
      // Discord appends/prepends <li> elements when loading new message batches.
      const obs = new MutationObserver((mutations) => {
        const anyAdded = mutations.some((m) => m.addedNodes.length > 0);
        if (anyAdded) {
          // Give React a small settle window to finish the render batch.
          setTimeout(finish, CFG.mutationSettle);
        }
      });
      obs.observe(ol, { childList: true });

      // Safety fallback: if no mutation fires, move on after the timeout.
      const fallback = setTimeout(finish, CFG.mutationTimeout);

      // Trigger scroll — this is what causes Discord to load older messages.
      scroller.scrollTop = 0;
    });
  }

  /**
   * Main collection loop.
   *
   * Strategy:
   *   1. Scan already-visible messages first.
   *   2. Call scrollAndWaitForLoad() which scrolls to the top and listens
   *      via MutationObserver for new <li> elements, rather than using a
   *      fixed sleep. This is faster when messages load quickly and more
   *      reliable when they are slow.
   *   3. After each scroll, check whether any new message IDs were seen.
   *      If not for CFG.maxNoNew consecutive attempts, we have reached the
   *      beginning of the channel history and stop.
   */
  async function runScrollLoop(targetUserId, maxScrolls, onStatus) {
    const scroller = findScroller();
    if (!scroller) {
      onStatus("⚠ Could not find the message scroller. Is a channel open?");
      return;
    }

    let noNewConsecutive = 0;
    let scrollsDone = 0;

    // Initial scan of the messages already rendered on screen.
    onStatus("Scanning visible messages…");
    processVisibleMessages(targetUserId);
    updateCounter();

    while (!shouldStop && scrollsDone < maxScrolls) {
      onStatus(`Scrolling up… (${scrollsDone + 1} / ${maxScrolls})`);

      const prevProcessed = processedMsgIds.size;

      // Scroll and wait — the MutationObserver inside resolves as soon as
      // Discord adds new <li> elements, so we don't over-sleep.
      await scrollAndWaitForLoad(scroller);

      processVisibleMessages(targetUserId);
      updateCounter();

      const newMsgs = processedMsgIds.size - prevProcessed;

      if (newMsgs === 0) {
        noNewConsecutive++;
        if (noNewConsecutive >= CFG.maxNoNew) {
          onStatus("Reached the top of the channel history.");
          break;
        }
      } else {
        noNewConsecutive = 0;
      }

      scrollsDone++;
      // Brief throttle between scroll cycles — duration controlled by the
      // speed slider and updated in real time via the `scrollDelay` variable.
      await sleep(scrollDelay);
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // EXPORT
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Trigger a browser download of all collected URLs as a plain-text file,
   * one URL per line.
   */
  function exportToTxt(userId, channelId) {
    if (urlsByMessage.size === 0) {
      alert("No media URLs were collected.");
      return;
    }

    const timestamp = new Date()
      .toISOString()
      .replace(/[:T]/g, "-")
      .replace(/\.\d{3}Z$/, "");

    const filename = `discord_attachments_${userId}_${channelId}_${timestamp}.txt`;

    // Build grouped output.
    // Each message = one block (1–N URLs joined by newline).
    // Blocks are separated by a single blank line.
    const blocks = [];
    urlsByMessage.forEach((urls) => {
      if (urls.length > 0) blocks.push(urls.join("\n"));
    });
    const content = blocks.join("\n\n");

    const blob = new Blob([content], { type: "text/plain" });
    const link = document.createElement("a");

    link.href = URL.createObjectURL(blob);
    link.download = filename;
    link.click();

    // Release the object URL after a short delay.
    setTimeout(() => URL.revokeObjectURL(link.href), 2000);
  }

  // ─────────────────────────────────────────────────────────────────────────
  // UI
  // ─────────────────────────────────────────────────────────────────────────
  let panelEl, statusEl, counterEl, startBtn, stopBtn, exportBtn;

  function updateCounter() {
    if (counterEl) {
      counterEl.innerHTML =
        `Messages scanned: <b>${messagesScanned}</b>&nbsp;&nbsp;` +
        `Images: <b>${imagesFound}</b>&nbsp;&nbsp;` +
        `Files: <b>${filesFound}</b>`;
    }
  }

  function setStatus(msg) {
    if (statusEl) statusEl.textContent = msg;
  }

  /** Inject the toggle button and floating panel into the Discord page. */
  function createUI() {
    // ── Styles injected once ──────────────────────────────────────────────
    const style = document.createElement("style");
    style.textContent = `
            #dac-toggle {
                position: fixed; top: 8px; right: 56px; z-index: 9999;
                width: 34px; height: 34px; border-radius: 50%; border: none;
                background: #5865F2; color: #fff; cursor: pointer;
                display: flex; align-items: center; justify-content: center;
                box-shadow: 0 2px 8px rgba(0,0,0,.45);
                transition: background .15s;
            }
            #dac-toggle:hover { background: #4752C4; }
            #dac-panel {
                position: fixed; top: 50px; right: 12px; z-index: 9998;
                width: 290px; background: #2B2D31; color: #DCDDDE;
                border: 1px solid #1E1F22; border-radius: 8px;
                padding: 16px; font-family: 'gg sans','Noto Sans',sans-serif;
                font-size: 14px; box-shadow: 0 4px 20px rgba(0,0,0,.55);
                display: none;
            }
            #dac-panel h3 {
                margin: 0 0 14px; font-size: 15px; color: #fff; font-weight: 700;
            }
            .dac-label {
                display: block; margin-bottom: 4px; font-size: 11px;
                color: #B5BAC1; font-weight: 700; text-transform: uppercase;
                letter-spacing: .04em;
            }
            .dac-input {
                width: 100%; box-sizing: border-box; background: #1E1F22;
                border: 1px solid #3F4147; border-radius: 4px;
                color: #DCDDDE; padding: 6px 8px; margin-bottom: 12px;
                font-size: 13px; outline: none; transition: border-color .15s;
            }
            .dac-input:focus { border-color: #5865F2; }
            .dac-btn {
                border: none; border-radius: 4px; padding: 7px 14px;
                cursor: pointer; font-size: 13px; font-weight: 600;
                color: #fff; transition: filter .15s;
            }
            .dac-btn:hover { filter: brightness(1.12); }
            .dac-btn:disabled { opacity: .4; cursor: not-allowed; filter: none; }
            #dac-start  { background: #248046; }
            #dac-stop   { background: #DA373C; display: none; }
            #dac-export { background: #5865F2; display: none; }
            #dac-status {
                margin: 10px 0 4px; font-size: 12px; color: #B5BAC1;
                min-height: 16px; word-break: break-word;
            }
            #dac-counter {
                font-size: 11px; color: #57F287; font-weight: 600;
                min-height: 14px;
            }
            .dac-btn-row { display: flex; gap: 6px; flex-wrap: wrap; }
        `;
    document.head.appendChild(style);

    // ── Toggle button (chat-bubble icon) ──────────────────────────────────
    const toggleBtn = document.createElement("button");
    toggleBtn.id = "dac-toggle";
    toggleBtn.title = "Discord Attachment Collector";
    toggleBtn.innerHTML = `
            <svg width="17" height="17" viewBox="0 0 24 24" fill="currentColor">
                <path d="M20 2H4a2 2 0 0 0-2 2v18l4-4h14a2 2 0 0 0
                         2-2V4a2 2 0 0 0-2-2z"/>
            </svg>`;

    // ── Floating panel ────────────────────────────────────────────────────
    panelEl = document.createElement("div");
    panelEl.id = "dac-panel";
    panelEl.innerHTML = `
            <h3>Attachment Collector</h3>

            <label class="dac-label" for="dac-channel">Channel ID</label>
            <input  class="dac-input" id="dac-channel"  placeholder="Channel ID" />

            <label class="dac-label" for="dac-userid">User ID</label>
            <input  class="dac-input" id="dac-userid" placeholder="e.g. 123456789012345678" />

            <label class="dac-label" for="dac-maxscroll">Max scroll attempts</label>
            <input  class="dac-input" id="dac-maxscroll" type="number"
                    min="1" max="2000" value="300" />

            <!-- Scroll speed slider — value persisted in localStorage -->
            <label class="dac-label" for="dac-speed">
                Scroll speed delay: <span id="dac-speed-val"></span>ms
            </label>
            <input class="dac-input" id="dac-speed" type="range"
                   min="100" max="2000" step="50"
                   style="padding:0; cursor:pointer;" />

            <div class="dac-btn-row">
                <button class="dac-btn" id="dac-start">▶ Start</button>
                <button class="dac-btn" id="dac-stop">■ Stop</button>
                <button class="dac-btn" id="dac-export">↓ Export .txt</button>
            </div>

            <div id="dac-status">Ready.</div>
            <div id="dac-counter"></div>
        `;

    document.body.append(toggleBtn, panelEl);

    // Grab references to dynamic elements
    statusEl = document.getElementById("dac-status");
    counterEl = document.getElementById("dac-counter");
    startBtn = document.getElementById("dac-start");
    stopBtn = document.getElementById("dac-stop");
    exportBtn = document.getElementById("dac-export");

    // ── Scroll speed slider ───────────────────────────────────────────────
    const speedSlider  = document.getElementById("dac-speed");
    const speedValSpan = document.getElementById("dac-speed-val");

    // Seed the slider with the value loaded from localStorage at startup.
    speedSlider.value    = scrollDelay;
    speedValSpan.textContent = scrollDelay;

    speedSlider.addEventListener("input", () => {
      // Update the runtime variable immediately so any in-progress scroll
      // loop picks up the new delay on the very next cycle.
      scrollDelay = parseInt(speedSlider.value);
      speedValSpan.textContent = scrollDelay;

      // Persist the new value so it survives page reloads.
      try { localStorage.setItem(SCROLL_DELAY_KEY, scrollDelay); } catch { /* storage blocked */ }
    });

    // ── Toggle panel open/close ───────────────────────────────────────────
    toggleBtn.addEventListener("click", () => {
      const isOpen = panelEl.style.display !== "none";
      panelEl.style.display = isOpen ? "none" : "block";
      // Refresh channel ID whenever the panel is opened (Discord is a SPA).
      if (!isOpen && !isRunning) {
        const ch = document.getElementById("dac-channel");
        if (ch) ch.value = getCurrentChannelId();
      }
    });

    // ── Start button ──────────────────────────────────────────────────────
    startBtn.addEventListener("click", async () => {
      const userId    = document.getElementById("dac-userid").value.trim();
      const channelId = document.getElementById("dac-channel").value.trim();
      const maxScrolls = Math.max(
        1,
        parseInt(document.getElementById("dac-maxscroll").value) || 300,
      );

      if (!userId) {
        alert("Please enter a User ID.");
        return;
      }
      if (!/^\d{10,20}$/.test(userId)) {
        alert("User ID must be a numeric Discord snowflake (10–20 digits).");
        return;
      }
      if (!channelId) {
        alert("Please enter a channel ID.");
        return;
      }

      // Reset state for a fresh run.
      isRunning = true;
      shouldStop = false;
      collectedUrls.clear();
      urlsByMessage.clear();
      processedMsgIds.clear();
      messagesScanned = 0;
      filesFound      = 0;
      imagesFound     = 0;
      updateCounter();

      startBtn.style.display = "none";
      stopBtn.style.display = "inline-block";
      exportBtn.style.display = "none";
      setStatus("Starting…");

      try {
        await runScrollLoop(userId, maxScrolls, setStatus);

        if (shouldStop) {
          setStatus(`Stopped. ${imagesFound} image(s), ${filesFound} file(s).`);
        } else {
          setStatus(`Done! ${imagesFound} image(s), ${filesFound} file(s).`);
        }
      } catch (err) {
        setStatus("Error: " + err.message);
        console.error("[DAC]", err);
      }

      isRunning = false;
      startBtn.style.display = "inline-block";
      stopBtn.style.display  = "none";
      if (urlsByMessage.size > 0) exportBtn.style.display = "inline-block";
    });

    // ── Stop button ───────────────────────────────────────────────────────
    stopBtn.addEventListener("click", () => {
      shouldStop = true;
      setStatus("Stopping after current scroll…");
    });

    // ── Export button ─────────────────────────────────────────────────────
    exportBtn.addEventListener("click", () => {
      const userId    = document.getElementById("dac-userid").value.trim();
      const channelId = document.getElementById("dac-channel").value.trim();
      exportToTxt(userId, channelId);
    });
  }

  // ─────────────────────────────────────────────────────────────────────────
  // INIT
  // Wait until Discord's React app has mounted before injecting the UI.
  // Discord is a SPA, so the DOM may not be ready at document-idle.
  // ─────────────────────────────────────────────────────────────────────────
  function init() {
    if (document.getElementById("dac-toggle")) return; // already injected

    if (!document.querySelector("#app-mount")) {
      // App not mounted yet — retry shortly.
      setTimeout(init, 600);
      return;
    }

    createUI();

    // Re-check if the toggle button got removed during a hot-reload / SPA
    // navigation (unlikely but defensive).
    const observer = new MutationObserver(() => {
      if (!document.getElementById("dac-toggle")) createUI();
    });
    observer.observe(document.body, { childList: true });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
