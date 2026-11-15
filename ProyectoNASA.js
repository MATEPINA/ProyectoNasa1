/* =========================================================
   Ares-360 · HUD táctico de EVA (MarsWalk · NASA Space Apps)
   JavaScript puro + Pannellum (360°) + Leaflet (minimapa)
   ========================================================= */
'use strict';
(() => {
  // ---------- Utilidades ----------
  const $ = (s, r = document) => r.querySelector(s);
  const RAD = Math.PI / 180;
  const norm360 = a => ((a % 360) + 360) % 360;
  const norm180 = a => { a = norm360(a); return a > 180 ? a - 360 : a; };
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const lerp = (a, b, t) => a + (b - a) * t;
  const pad3 = n => String(Math.round(norm360(n)) % 360).padStart(3, '0');
  const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const tick = () => new Promise(r => setTimeout(r, 16));
  const FONT = '"Cascadia Mono", Consolas, monospace';
  const CARD = ['N', 'NE', 'E', 'SE', 'S', 'SO', 'O', 'NO'];

  function mulberry32(a) {
    return function () {
      a |= 0; a = a + 0x6D2B79F5 | 0;
      let t = Math.imul(a ^ a >>> 15, 1 | a);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }

  // ---------- Estado global ----------
  const S = {
    data: null, P: [], U: null, R: 3389500, idx: 0,
    viewer: null, map: null, capas: {}, modo: 0,
    pano: {}, heading: -1, hfov: -1, dpr: Math.min(window.devicePixelRatio || 1, 2),
  };
  // El modo 'hipso' solo se ofrece si existe la capa real (ver initMapa)
  const MODOS_TODOS = [
    { id: 'satelital', label: 'SATÉLITE REAL' },
    { id: 'hipso', label: 'MAPA HIPSOMÉTRICO' },
    { id: 'pendiente', label: 'PENDIENTES Y OBSTÁCULOS' },
    { id: 'hidratacion', label: 'HIDRATACIÓN MINERAL / ISRU' },
  ];
  let MODOS = MODOS_TODOS;
  const RAMPAS = {
    pendiente: { min: 0, max: 35, unidad: '°', stops: [[0, [48, 209, 88]], [0.34, [255, 214, 10]], [0.57, [255, 159, 10]], [0.7, [255, 59, 48]], [1, [170, 0, 40]]] },
    hidratacion: { min: 0, max: 8, unidad: '% H₂O', stops: [[0, [20, 70, 170]], [0.5, [0, 200, 255]], [1, [225, 255, 255]]] },
  };
  const HIDR_DEF = 3, DENSIDAD_REGOLITO = 1500;   // % H₂O de respaldo · kg/m³ (para L/m³ extraíbles)

  // ---------- Geodesia marciana ----------
  function rumbo(a, b) {
    const f1 = a.lat * RAD, f2 = b.lat * RAD, dl = (b.lon - a.lon) * RAD;
    const y = Math.sin(dl) * Math.cos(f2);
    const x = Math.cos(f1) * Math.sin(f2) - Math.sin(f1) * Math.cos(f2) * Math.cos(dl);
    return norm360(Math.atan2(y, x) / RAD);
  }
  function distancia(a, b) {
    const df = (b.lat - a.lat) * RAD, dl = (b.lon - a.lon) * RAD;
    const h = Math.sin(df / 2) ** 2 + Math.cos(a.lat * RAD) * Math.cos(b.lat * RAD) * Math.sin(dl / 2) ** 2;
    return 2 * S.R * Math.asin(Math.sqrt(h));
  }
  const porId = id => S.P.find(p => p.id === id);
  const numOr = (v, d) => (typeof v === 'number' && Number.isFinite(v) ? v : d);
  const hidrDe = p => numOr(p.hidratacion_pct, HIDR_DEF);
  const aguaDe = p => hidrDe(p) / 100 * DENSIDAD_REGOLITO;   // 1 kg H₂O ≈ 1 L
  // Hotspot de peligro: tipo "peligro" explícito, o "terreno" por encima del umbral de pendiente
  const esPeligro = h => h.tipo === 'peligro' || (h.tipo === 'terreno' && h.pendiente_grados > S.U.pendiente_peligro_grados);
  const fmtPend = h => Number.isFinite(h.pendiente_grados) ? h.pendiente_grados.toFixed(1) + '°' : '—';
  const fmtLat = v => `${Math.abs(v).toFixed(4)}°${v < 0 ? 'S' : 'N'}`;
  const fmtLon = v => `${Math.abs(v).toFixed(4)}°${v < 0 ? 'O' : 'E'}`;
  const nivelTerreno = e => /^PELIGRO/i.test(e || '') ? 'crit' : /^PRECAUCI/i.test(e || '') ? 'warn' : 'ok';
  // Punto peligroso: pendiente del entorno sobre el umbral o terreno declarado PELIGRO
  const puntoPeligro = p => p.pendiente_max_grados > S.U.pendiente_peligro_grados || nivelTerreno(p.navegacion?.estadoTerreno) === 'crit';

  // Adaptador: estructura del JSON (coordenadas / navegacion / ambiente / eva) → campos planos
  // que usan la geodesia, los campos sintéticos y el minimapa. El JSON original no se toca.
  function normalizarPunto(p) {
    const c = p.coordenadas || {}, n = p.navegacion || {}, a = p.ambiente || {}, e = p.eva || {};
    p.lat = numOr(c.lat, p.lat);
    p.lon = numOr(c.lng, p.lon);
    p.elevacion_m = numOr(c.elevacionMOLA, p.elevacion_m);
    p.pendiente_grados = Math.abs(numOr(n.pendienteLocalGrados, p.pendiente_grados ?? 0));
    p.pendiente_max_grados = numOr(n.pendienteMaximaEntornoGrados, p.pendiente_grados);
    p.oxigeno_pct = numOr(e.oxigeno_pct, numOr(p.oxigeno_pct, 100));
    p.radiacion_acumulada_msv = numOr(e.radiacion_acumulada_msv, numOr(p.radiacion_acumulada_msv, 0));
    p.hidratacion_pct = numOr(e.hidratacion_pct, p.hidratacion_pct);
    const dosisDia = a.radiacion?.dosisRADmSvDia;
    p.tasa_dosis_usv_h = Number.isFinite(dosisDia) ? dosisDia * 1000 / 24 : numOr(p.tasa_dosis_usv_h, 0);
    return p;
  }

  // =========================================================
  //  ARRANQUE
  // =========================================================
  function bootMsg(msg, pct) {
    $('#boot-msg').textContent = msg;
    if (pct != null) $('#boot-fill').style.width = pct + '%';
  }
  function fatal(html) {
    const m = $('#boot-msg');
    m.classList.add('err'); m.innerHTML = '⚠ ' + html;
    $('#boot').classList.remove('out');
    $('#boot-fill').style.background = 'var(--alert)';
  }
  function ocultarBoot() { bootMsg('SISTEMAS NOMINALES', 100); setTimeout(() => $('#boot').classList.add('out'), 350); }

  async function boot() {
    if (location.protocol === 'file:') {
      return fatal('Esta app debe abrirse desde un servidor local, no con doble clic.<br><br>En la carpeta del proyecto ejecuta:<br><code>python -m http.server 8080</code><br>y abre <code>http://localhost:8080</code>');
    }
    if (typeof pannellum === 'undefined' || typeof L === 'undefined') {
      return fatal('No se pudieron cargar Pannellum/Leaflet. La primera carga necesita conexión a Internet; después funciona offline.');
    }
    registrarSW(); relojMarte(); conectividad();

    try {
      bootMsg('ENLACE CON BASE DE DATOS DE RUTA…', 10);
      const r = await fetch('datos_ruta.json');
      if (!r.ok) throw new Error('HTTP ' + r.status);
      S.data = await r.json();
    } catch (e) {
      return fatal('No se pudo cargar <code>datos_ruta.json</code>: ' + esc(e.message));
    }
    S.P = S.data.puntos.map(normalizarPunto);
    S.U = S.data.mision.umbrales;
    S.R = S.data.mision.radio_marte_m || S.R;
    const A = S.data.mision.assets;

    for (let i = 0; i < S.P.length; i++) {
      const p = S.P[i];
      bootMsg(`RECONSTRUYENDO TERRENO ${p.id.toUpperCase()} · ${p.nombre.toUpperCase()}…`, 20 + i * 20);
      await tick();
      S.pano[p.id] = A.usar_imagenes_reales ? p.imagen : await generarPanorama(p, i);
    }
    bootMsg('DESPLEGANDO MINIMAPA TÁCTICO…', 85); await tick();
    initMapa();
    initUI();
    bootMsg('ACOPLANDO VISOR 360°…', 92); await tick();
    initVisor();
    requestAnimationFrame(bucle);
  }

  // =========================================================
  //  PLACEHOLDER: PANORAMA EQUIRECTANGULAR MARCIANO (Canvas)
  // =========================================================
  function perfilPeriodico(W, seed, fmin, fmax, n) {
    const r = mulberry32(seed), comps = [];
    for (let j = 0; j < n; j++) {
      const f = Math.round(fmin + r() * (fmax - fmin));
      comps.push([f, r() * Math.PI * 2, 1 / Math.sqrt(f)]);
    }
    const sum = comps.reduce((a, c) => a + c[2], 0);
    return x => { let v = 0; for (const [f, ph, a] of comps) v += a * Math.sin(2 * Math.PI * f * x / W + ph); return v / sum; };
  }

  function generarPanorama(p, i) {
    const W = 4096, H = 2048, hz = H / 2;
    const c = document.createElement('canvas'); c.width = W; c.height = H;
    const g = c.getContext('2d');
    const rnd = mulberry32(4242 + i * 977);
    const rp = p.render_placeholder || {};
    const rug = rp.rugosidad ?? 0.5;
    const xDeRumbo = r => ((norm180(r - p.rumbo_centro) + 180) / 360) * W;
    const rumboDeX = x => norm360(p.rumbo_centro + (x / W) * 360 - 180);
    const bump = x => {
      if (rp.relieve_rumbo == null) return 0;
      const d = Math.abs(norm180(rumboDeX(x) - rp.relieve_rumbo));
      return Math.exp(-((d / 38) ** 2));
    };

    // Cielo color caramelo marciano
    let gr = g.createLinearGradient(0, 0, 0, hz);
    gr.addColorStop(0, '#1a1210'); gr.addColorStop(0.4, '#5e3b2b');
    gr.addColorStop(0.8, '#bb8660'); gr.addColorStop(1, '#dcae86');
    g.fillStyle = gr; g.fillRect(0, 0, W, hz);

    // Sol (más pequeño que en la Tierra, con halo azulado)
    const sx = xDeRumbo(rp.sol_rumbo ?? 120), sy = hz * 0.42;
    for (const off of [-W, 0, W]) {
      let sg = g.createRadialGradient(sx + off, sy, 0, sx + off, sy, 320);
      sg.addColorStop(0, 'rgba(255,246,230,.75)'); sg.addColorStop(0.08, 'rgba(200,220,255,.35)');
      sg.addColorStop(0.3, 'rgba(230,180,140,.12)'); sg.addColorStop(1, 'rgba(0,0,0,0)');
      g.fillStyle = sg; g.fillRect(sx + off - 320, sy - 320, 640, 640);
    }

    // Capa lejana: borde del cráter visible bajo en todo el horizonte (placeholder)
    const pf = perfilPeriodico(W, 11 + i, 2, 30, 14);
    const pm = perfilPeriodico(W, 91 + i, 3, 60, 18);
    const pn = perfilPeriodico(W, 171 + i, 8, 120, 22);
    const capa = (fy, colTop, colBot, alto) => {
      g.beginPath(); g.moveTo(0, hz + 2);
      for (let x = 0; x <= W; x += 4) g.lineTo(x, hz - fy(x));
      g.lineTo(W, hz + 2); g.closePath();
      const lg = g.createLinearGradient(0, hz - alto, 0, hz);
      lg.addColorStop(0, colTop); lg.addColorStop(1, colBot);
      g.fillStyle = lg; g.fill();
    };
    capa(x => 22 + 26 * (pf(x) + 1) / 2, '#a77a5e', '#8e644a', 60);
    capa(x => 6 + 18 * (pm(x) + 1) / 2 * rug + bump(x) * (rp.relieve_altura || 0) * H, '#7b4c35', '#6a3f2c', 220);
    capa(x => 2 + 8 * (pn(x) + 1) / 2 * rug + bump(x) * (rp.relieve_altura || 0) * H * 0.35, '#6a3d29', '#7d4a31', 120);

    // Estratos en el relieve (delta/crestas)
    if ((rp.relieve_altura || 0) > 0.05) {
      g.save(); g.globalAlpha = 0.18; g.strokeStyle = '#d8a27a'; g.lineWidth = 2;
      for (let k = 1; k < 10; k++) {
        g.beginPath();
        for (let x = 0; x <= W; x += 8) {
          const b = bump(x); if (b < 0.25) { g.moveTo(x, hz); continue; }
          g.lineTo(x, hz - b * rp.relieve_altura * H * (k / 11) - pm(x) * 6);
        }
        g.stroke();
      }
      g.restore();
    }

    // Suelo
    gr = g.createLinearGradient(0, hz, 0, H);
    gr.addColorStop(0, '#9c6544'); gr.addColorStop(0.35, '#7a4630');
    gr.addColorStop(0.8, '#3d2216'); gr.addColorStop(1, '#1a0e09');
    g.fillStyle = gr; g.fillRect(0, hz, W, hz);

    // Textura de regolito
    for (let k = 0; k < 60000; k++) {
      const y = hz + Math.pow(rnd(), 1.25) * hz;
      const t = (y - hz) / hz;
      const s = 1 + t * 3 * rnd();
      g.fillStyle = rnd() < 0.5 ? `rgba(30,14,8,${0.1 + 0.15 * rnd()})` : `rgba(230,170,120,${0.05 + 0.1 * rnd()})`;
      g.fillRect(rnd() * W, y, s, s * 0.6);
    }
    // Ondulaciones eólicas
    g.save(); g.lineWidth = 3;
    for (let k = 0; k < 40; k++) {
      const y0 = hz + 30 + Math.pow(rnd(), 1.6) * hz * 0.6, x0 = rnd() * W, len = 200 + rnd() * 700;
      g.strokeStyle = `rgba(${rnd() < 0.5 ? '40,20,12' : '220,160,110'},.12)`;
      g.beginPath();
      for (let x = 0; x <= len; x += 10) g.lineTo((x0 + x) % W, y0 + Math.sin(x / 40) * 4);
      g.stroke();
    }
    g.restore();

    // Rocas (más grandes cuanto más cerca)
    const nRocas = Math.round(220 + rug * 260);
    for (let k = 0; k < nRocas; k++) {
      const y = hz + 6 + Math.pow(rnd(), 1.7) * hz * 0.9;
      const t = (y - hz) / hz;
      const r = (2 + t * t * 80 * (0.3 + rnd())) * (0.6 + rug * 0.6);
      const x = rnd() * W;
      const tono = 60 + rnd() * 50;
      const dib = (xx) => {
        g.fillStyle = 'rgba(15,6,3,.45)';
        g.beginPath(); g.ellipse(xx + r * 0.35, y + r * 0.25, r * 1.1, r * 0.4, 0, 0, Math.PI * 2); g.fill();
        g.fillStyle = `rgb(${tono + 25},${tono * 0.6},${tono * 0.42})`;
        g.beginPath(); g.ellipse(xx, y, r, r * (0.45 + rnd() * 0.25), 0, Math.PI, 0); g.lineTo(xx + r, y); g.ellipse(xx, y, r, r * 0.22, 0, 0, Math.PI); g.fill();
        g.fillStyle = 'rgba(255,215,170,.18)';
        g.beginPath(); g.ellipse(xx - r * 0.3, y - r * 0.18, r * 0.45, r * 0.16, -0.3, 0, Math.PI * 2); g.fill();
      };
      dib(x);
      if (x < r * 2) dib(x + W);
      if (x > W - r * 2) dib(x - W);
    }

    // Overlay de calibración: horizonte y rumbos
    g.save();
    g.strokeStyle = 'rgba(0,240,255,.25)'; g.lineWidth = 1;
    g.beginPath(); g.moveTo(0, hz); g.lineTo(W, hz); g.stroke();
    g.font = `bold 30px ${FONT}`; g.textAlign = 'center'; g.fillStyle = 'rgba(0,240,255,.55)';
    for (let r = 0; r < 360; r += 15) {
      const x = xDeRumbo(r);
      g.beginPath(); g.moveTo(x, hz + 4); g.lineTo(x, hz + (r % 45 ? 14 : 28)); g.stroke();
      if (r % 45 === 0) g.fillText(CARD[r / 45], x, hz + 62);
    }
    g.font = `bold 34px ${FONT}`; g.fillStyle = 'rgba(0,240,255,.18)';
    for (let r = 0; r < 360; r += 90) g.fillText(`PLACEHOLDER · ${p.imagen}`, xDeRumbo(r + 45), hz + hz * 0.5);
    g.restore();

    return new Promise(res => c.toBlob(b => res(URL.createObjectURL(b)), 'image/jpeg', 0.9));
  }

  // =========================================================
  //  PLACEHOLDER: RECORTE SATELITAL (Canvas)
  // =========================================================
  function aspectoMapa(lim) {
    const latSpan = lim[1][0] - lim[0][0], lonSpan = lim[1][1] - lim[0][1];
    const latC = (lim[0][0] + lim[1][0]) / 2;
    return (lonSpan * Math.cos(latC * RAD)) / latSpan;
  }
  function proyector(lim, w, h) {
    return {
      x: lon => (lon - lim[0][1]) / (lim[1][1] - lim[0][1]) * w,
      y: lat => (lim[1][0] - lat) / (lim[1][0] - lim[0][0]) * h,
      lon: x => lim[0][1] + x / w * (lim[1][1] - lim[0][1]),
      lat: y => lim[1][0] - y / h * (lim[1][0] - lim[0][0]),
    };
  }

  function generarMapa(lim) {
    const w = 1024, h = Math.round(1024 / aspectoMapa(lim));
    const c = document.createElement('canvas'); c.width = w; c.height = h;
    const g = c.getContext('2d'), rnd = mulberry32(777), P = proyector(lim, w, h);

    g.fillStyle = '#5a3a2a'; g.fillRect(0, 0, w, h);
    for (let k = 0; k < 600; k++) {
      const x = rnd() * w, y = rnd() * h, r = 20 + rnd() * 120;
      const gg = g.createRadialGradient(x, y, 0, x, y, r);
      const claro = rnd() < 0.5;
      gg.addColorStop(0, claro ? 'rgba(190,130,95,.10)' : 'rgba(25,12,8,.12)'); gg.addColorStop(1, 'rgba(0,0,0,0)');
      g.fillStyle = gg; g.fillRect(x - r, y - r, r * 2, r * 2);
    }
    // Delta (oeste): abanico claro con lóbulos
    const fx = P.x(S.geo.frente);
    for (let k = 0; k < 7; k++) {
      g.fillStyle = `rgba(${165 + k * 6},${112 + k * 4},${80 + k * 3},.28)`;
      g.beginPath();
      g.ellipse(-40, h * (0.2 + rnd() * 0.5), fx + 20 + rnd() * 60, h * (0.25 + rnd() * 0.2), (rnd() - 0.5) * 0.6, -Math.PI / 2, Math.PI / 2);
      g.fill();
    }
    g.strokeStyle = 'rgba(40,20,12,.5)'; g.lineWidth = 3; g.beginPath();
    for (let y = 0; y <= h; y += 6) g.lineTo(fx + Math.sin(y / 30) * 12 + Math.sin(y / 9) * 4, y);
    g.stroke();
    // Canales fósiles sobre el delta
    g.strokeStyle = 'rgba(230,180,140,.25)'; g.lineWidth = 2;
    for (let k = 0; k < 6; k++) {
      g.beginPath(); let y = h * (0.1 + rnd() * 0.8);
      for (let x = 0; x < fx; x += 6) { y += (rnd() - 0.5) * 8; g.lineTo(x, y); }
      g.stroke();
    }
    // Séítah (sur): crestas paralelas oscuras
    g.strokeStyle = 'rgba(30,14,9,.35)'; g.lineWidth = 2;
    const sy = P.y(S.geo.cresta);
    for (let k = 0; k < 70; k++) {
      const x0 = P.x(S.geo.frente + 0.08 * S.geo.lonS) + rnd() * (w * 0.55), y0 = sy + rnd() * (h - sy);
      g.beginPath(); g.moveTo(x0, y0); g.quadraticCurveTo(x0 + 20, y0 - 8, x0 + 40 + rnd() * 30, y0 - 4); g.stroke();
    }
    // Cráteres
    for (let k = 0; k < 80; k++) {
      const x = rnd() * w, y = rnd() * h, r = 3 + Math.pow(rnd(), 3) * 30;
      g.fillStyle = 'rgba(20,9,5,.35)'; g.beginPath(); g.arc(x, y, r, 0, Math.PI * 2); g.fill();
      g.strokeStyle = 'rgba(220,170,130,.35)'; g.lineWidth = Math.max(1, r / 6);
      g.beginPath(); g.arc(x, y, r, Math.PI * 0.1, Math.PI * 1.1); g.stroke();
    }
    // Retícula
    g.strokeStyle = 'rgba(0,240,255,.08)'; g.lineWidth = 1;
    for (let x = 0; x < w; x += 64) { g.beginPath(); g.moveTo(x, 0); g.lineTo(x, h); g.stroke(); }
    for (let y = 0; y < h; y += 64) { g.beginPath(); g.moveTo(0, y); g.lineTo(w, y); g.stroke(); }
    g.font = `bold 16px ${FONT}`; g.fillStyle = 'rgba(0,240,255,.35)';
    g.fillText(`PLACEHOLDER · ${S.data.mision.assets.mapa || 'assets/mapa_gale.jpg'}`, 16, h - 16);
    return c.toDataURL('image/png');
  }

  // ---------- Campos de pendiente / hidratación mineral ----------
  // Referencia geográfica relativa a los límites del mapa (funciona con Gale, Jezero, etc.)
  function geoRef(lim) {
    const latS = lim[1][0] - lim[0][0], lonS = lim[1][1] - lim[0][1];
    const anchoM = distancia({ lat: lim[0][0], lon: lim[0][1] }, { lat: lim[0][0], lon: lim[1][1] });
    return {
      latC: (lim[0][0] + lim[1][0]) / 2, lonC: (lim[0][1] + lim[1][1]) / 2, latS, lonS,
      frente: lim[0][1] + 0.3 * lonS,      // escarpe/rasgo ficticio del placeholder
      cresta: lim[0][0] + 0.42 * latS,     // zona de crestas ficticia del placeholder
      sigma: Math.max(40, anchoM * 0.08),  // radio de influencia de cada medición (m)
    };
  }
  function fondoCampo(tipo, lat, lon) {
    const G = S.geo, nx = (lon - G.lonC) / G.lonS, ny = (lat - G.latC) / G.latS;   // -0.5..0.5
    const x = nx * 35, y = ny * 25;
    if (tipo === 'pendiente') {
      // Cráter Gale: llanura casi plana al NO que se empina hacia Monte Sharp (SE),
      // con una banda de crestas/dunas NE-SO en la transición (sintético)
      const s = nx - ny;   // -1 (NO) .. +1 (SE)
      let v = 4 + 7 * s + 2 * Math.sin(x * 1.9 + 1.3) * Math.cos(y * 2.3) + 1.5 * Math.sin(x * 5.1 + y * 4.2);
      v += 9 * Math.exp(-(((s - 0.3) / 0.12) ** 2)) * (0.7 + 0.3 * Math.sin(x * 4 + y * 4));
      return Math.max(0, v);
    }
    // hidratación (% H₂O ligada): aumenta suavemente hacia los estratos de Monte Sharp
    return clamp(2.4 + 1.2 * (nx - ny) + 0.6 * Math.sin(x * 1.1 + 0.7) * Math.cos(y * 1.5) + 0.3 * Math.sin(x * 3.7 + y * 2.9), 0, 100);
  }
  // El campo de pendiente se fuerza a la pendiente MÁXIMA del entorno de cada punto (zonas >20° en rojo)
  const valorPunto = (tipo, p) => tipo === 'pendiente' ? p.pendiente_max_grados : hidrDe(p);
  function valorCampo(tipo, lat, lon) {
    let v = fondoCampo(tipo, lat, lon);
    const s2 = 2 * S.geo.sigma * S.geo.sigma;
    for (const p of S.P) {
      const d = distancia({ lat, lon }, p);
      v += (valorPunto(tipo, p) - fondoCampo(tipo, p.lat, p.lon)) * Math.exp(-(d * d) / s2);
    }
    return v;
  }
  function colorRampa(tipo, v) {
    const R = RAMPAS[tipo], t = clamp((v - R.min) / (R.max - R.min), 0, 1);
    let i = 0;
    while (i < R.stops.length - 2 && t > R.stops[i + 1][0]) i++;
    const [t0, c0] = R.stops[i], [t1, c1] = R.stops[i + 1];
    const k = clamp((t - t0) / (t1 - t0 || 1), 0, 1);
    return c0.map((c, j) => Math.round(lerp(c, c1[j], k)));
  }
  function generarCampo(tipo, lim) {
    const w = 170, h = Math.round(170 / aspectoMapa(lim));
    const c = document.createElement('canvas'); c.width = w; c.height = h;
    const g = c.getContext('2d'), img = g.createImageData(w, h), P = proyector(lim, w, h);
    const U = S.U.pendiente_peligro_grados;
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const v = valorCampo(tipo, P.lat(y + 0.5), P.lon(x + 0.5));
      let [r, gg, b] = colorRampa(tipo, v), a;
      if (tipo === 'pendiente') {
        // Sólo se resalta lo que importa: tenue en precaución, rojo sólido sobre el umbral
        if (v > U) { r = 255; gg = 45; b = 45; a = 215; }
        else a = clamp((v - 6) / (U - 6), 0, 1) * 110;
      } else {
        // Aura cian: transparente donde hay poca agua ligada, brillante donde hay mucha
        a = clamp((v - RAMPAS.hidratacion.min) / (RAMPAS.hidratacion.max - RAMPAS.hidratacion.min), 0, 1) ** 1.4 * 235;
      }
      const o = (y * w + x) * 4;
      img.data[o] = r; img.data[o + 1] = gg; img.data[o + 2] = b; img.data[o + 3] = a;
    }
    g.putImageData(img, 0, 0);
    if (tipo === 'pendiente') {   // contorno blanco del umbral
      g.fillStyle = 'rgba(255,255,255,.55)';
      for (let y = 1; y < h; y++) for (let x = 1; x < w; x++) {
        const a = valorCampo(tipo, P.lat(y), P.lon(x)) > U;
        const b = valorCampo(tipo, P.lat(y), P.lon(x - 1)) > U;
        if (a !== b) g.fillRect(x, y, 1, 1);
      }
    }
    return c.toDataURL('image/png');
  }

  // =========================================================
  //  VISOR 360° (Pannellum)
  // =========================================================
  function hotspotsDe(p) {
    const hs = [];
    (p.conexiones || []).forEach(id => {
      const n = porId(id); if (!n) return;
      const b = rumbo(p, n), d = distancia(p, n);
      // Mantener la flecha dentro del campo vertical de panorámicas parciales
      const vaov = S.data.mision.assets.usar_imagenes_reales ? (p.vaov || 180) : 180;
      hs.push({
        id: 'nav-' + id, type: 'info', pitch: Math.max(-17, -vaov / 2 + 8), yaw: norm180(b - p.rumbo_centro),
        cssClass: 'hs-nav', createTooltipFunc: tipNav, createTooltipArgs: { n, b, d },
        clickHandlerFunc: () => irA(S.P.indexOf(n)),
      });
    });
    (p.hotspots || []).forEach((h, k) => {
      const peligro = esPeligro(h);
      const cls = h.tipo === 'ciencia' ? 'hs-sci' : (peligro ? 'hs-danger' : 'hs-terrain');
      hs.push({
        id: `hs-${p.id}-${k}`, type: 'info', pitch: h.pitch, yaw: h.yaw, cssClass: cls,
        createTooltipFunc: tipDato, createTooltipArgs: { h, peligro },
        clickHandlerFunc: () => mostrarDetalle(h, peligro),
      });
    });
    return hs;
  }
  function tipNav(div, a) {
    div.innerHTML = `<div class="hs-ring"></div><div class="hs-arrow"></div><div class="hs-arrow b"></div>
      <div class="hs-label">▲ ${esc(a.n.id.toUpperCase())} · ${esc(a.n.nombre)}<small>${Math.round(a.d)} m · RUMBO ${pad3(a.b)}°</small></div>`;
  }
  const recortar = (s, n) => { s = String(s ?? ''); return s.length > n ? s.slice(0, n - 1).trimEnd() + '…' : s; };
  function tipDato(div, a) {
    const h = a.h, sci = h.tipo === 'ciencia';
    const icon = sci ? '◆' : (a.peligro ? '⚠' : '▲');
    const sub = sci ? `${esc(h.instrumento || 'CRISM')} · ${esc(h.mineral)} · ${Math.round(numOr(h.confianza, 0) * 100)}%`
      : `${a.peligro ? 'PELIGRO · ' : ''}PENDIENTE ${fmtPend(h)}`;
    const hall = h.hallazgo || h.descripcion;
    div.innerHTML = `<div class="hs-ring"></div><div class="hs-core"><span>${icon}</span></div>
      <div class="hs-label">${esc(h.titulo)}<small>${sub}</small>${hall ? `<small class="hs-hall">${esc(recortar(hall, 72))}</small>` : ''}</div>`;
  }

  function initVisor() {
    const scenes = {};
    S.P.forEach(p => {
      // Panorámicas reales parciales: 360° en horizontal, vaov = 360·alto/ancho (calculado al optimizarlas)
      const vaov = S.data.mision.assets.usar_imagenes_reales ? (p.vaov || 180) : 180;
      scenes[p.id] = {
        type: 'equirectangular', panorama: S.pano[p.id], northOffset: p.rumbo_centro,
        // Pannellum no limita el pitch de panorámicas parciales por sí solo: sin minPitch/maxPitch
        // se ve el fondo negro y avoidShowingBackground calcula hfov = NaN
        haov: 360, vaov, vOffset: 0, minPitch: -vaov / 2, maxPitch: vaov / 2,
        hfov: 100, pitch: -4, yaw: 0, hotSpots: hotspotsDe(p),
      };
    });
    S.viewer = pannellum.viewer('pano', {
      default: {
        firstScene: S.P[0].id, sceneFadeDuration: 900, autoLoad: true, avoidShowingBackground: true,
        showControls: false, compass: false, minHfov: 45, maxHfov: 120, friction: 0.15,
        strings: { loadingLabel: 'CARGANDO PANORAMA…', loadButtonLabel: 'CARGAR' },
      },
      scenes,
    });
    let primera = true;
    S.viewer.on('load', () => { if (primera) { primera = false; ocultarBoot(); } });
    S.viewer.on('scenechange', id => alCambiarPunto(S.P.findIndex(p => p.id === id)));
    S.viewer.on('error', m => fatal('Error del visor 360°: ' + esc(m) + '<br>Revisa los nombres de archivo en <code>assets/README.txt</code>.'));
    alCambiarPunto(0);
  }

  function irA(i) {
    if (!S.viewer || i < 0 || i >= S.P.length || i === S.idx) return;
    const from = S.P[S.idx], to = S.P[i];
    const llegada = norm180(rumbo(from, to) - to.rumbo_centro); // mirar en la dirección de marcha
    S.viewer.loadScene(to.id, -4, llegada, 100);
  }

  function alCambiarPunto(i) {
    if (i < 0) return;
    S.idx = i;
    const p = S.P[i];
    actualizarTelemetria(p);
    actualizarMapaPunto(p);
    actualizarNav();
    actualizarAlertas(p);
    cerrarDetalle();
    S.heading = -1; // fuerza redibujado
  }

  // =========================================================
  //  TELEMETRÍA
  // =========================================================
  function animarNumero(el, to, dec) {
    const from = parseFloat(el.dataset.v || 0), t0 = performance.now(), dur = 900;
    el.dataset.v = to;
    const f = t => {
      const k = clamp((t - t0) / dur, 0, 1), e = 1 - Math.pow(1 - k, 3);
      el.textContent = (from + (to - from) * e).toFixed(dec);
      if (k < 1) requestAnimationFrame(f);
    };
    requestAnimationFrame(f);
  }
  function setMetrica(id, val, max, estado, dec) {
    const el = $('#' + id);
    el.classList.remove('ok', 'warn', 'crit'); el.classList.add(estado);
    el.querySelector('.fill').style.width = clamp(val / max * 100, 0, 100) + '%';
    animarNumero(el.querySelector('.v'), val, dec);
  }
  function recorridoHasta(i) {
    let d = 0;
    for (let k = 1; k <= i; k++) d += distancia(S.P[k - 1], S.P[k]);
    return d;
  }
  const setTxt = (sel, txt, title) => { const el = $(sel); if (!el) return; el.textContent = txt; if (title != null) el.title = title; };
  const fmtNum = (v, dec = 0, u = '') => Number.isFinite(v) ? `${v.toFixed(dec)}${u}` : '—';

  function actualizarTelemetria(p) {
    const U = S.U, SLOPE_MAX = 35;
    const nav = p.navegacion || {}, amb = p.ambiente || {};
    const ta = amb.temperaturaAireC || {}, hr = amb.humedadRelativaPorcentaje || {};
    const vi = amb.viento || {}, rad = amb.radiacion || {};
    $('#t-punto').textContent = `${p.id.toUpperCase()} / ${S.P.length}`;
    $('#t-nombre').textContent = p.nombre;
    $('#t-sub').textContent = p.subtitulo || '';
    $('#t-coords').textContent = `GPS ${fmtLat(p.lat)} · ${fmtLon(p.lon)}`;
    const ter = $('#t-terreno');
    if (ter) {
      ter.className = 'terreno ' + nivelTerreno(nav.estadoTerreno);
      ter.textContent = nav.estadoTerreno || '—';
      ter.hidden = !nav.estadoTerreno;
    }

    setMetrica('m-o2', p.oxigeno_pct, 100,
      p.oxigeno_pct < U.oxigeno_critico_pct ? 'crit' : p.oxigeno_pct < U.oxigeno_bajo_pct ? 'warn' : 'ok', 0);
    const min = Math.round(p.oxigeno_pct / 100 * (U.autonomia_total_min || 480));
    $('#t-auto').textContent = `${Math.floor(min / 60)} h ${String(min % 60).padStart(2, '0')} min`;

    const lim = U.radiacion_limite_eva_msv, fr = p.radiacion_acumulada_msv / lim;
    setMetrica('m-rad', p.radiacion_acumulada_msv, lim, fr > 0.8 ? 'crit' : fr > 0.5 ? 'warn' : 'ok', 2);
    const dosisDia = rad.dosisRADmSvDia;
    $('#t-dosis').textContent = Number.isFinite(dosisDia)
      ? `${dosisDia.toFixed(2)} mSv/día (${p.tasa_dosis_usv_h.toFixed(1)} µSv/h)`
      : `${p.tasa_dosis_usv_h.toFixed(1)} µSv/h`;
    $('#t-lim').textContent = lim.toFixed(1);
    setTxt('#t-uv', [rad.indiceUV && `UV ${rad.indiceUV}`, rad.alertaSolar].filter(Boolean).join(' · ') || '—');

    setMetrica('m-slope', p.pendiente_grados, SLOPE_MAX,
      p.pendiente_grados > U.pendiente_peligro_grados ? 'crit' : p.pendiente_grados > U.pendiente_precaucion_grados ? 'warn' : 'ok', 1);
    $('#tick-prec').style.left = (U.pendiente_precaucion_grados / SLOPE_MAX * 100) + '%';
    $('#tick-pel').style.left = (U.pendiente_peligro_grados / SLOPE_MAX * 100) + '%';
    $('#t-umbral').textContent = U.pendiente_peligro_grados;
    const pmax = $('#t-pmax');
    if (pmax) {
      pmax.textContent = fmtNum(p.pendiente_max_grados, 1, '°');
      pmax.className = p.pendiente_max_grados > U.pendiente_peligro_grados ? 'crit' : '';
    }
    setTxt('#t-incl', fmtNum(nav.inclinacionLateralGrados, 1, '°'));

    // Hidratación mineral (agua ligada, % en peso) → litros extraíbles por m³ de regolito
    const hidr = clamp(hidrDe(p), 0, 100), agua = aguaDe(p), R = RAMPAS.hidratacion;
    const vh = $('#val-hidr'), bh = $('#bar-hidr');
    if (vh) vh.textContent = `${hidr.toFixed(1)}% · ${Math.round(agua)} L/m³`;
    if (bh) bh.style.width = clamp((hidr - R.min) / (R.max - R.min) * 100, 0, 100) + '%';

    setTxt('#t-elev', fmtNum(p.elevacion_m, 0, ' m'));
    setTxt('#t-pres', fmtNum(amb.presionPa, 0, ' Pa'));
    setTxt('#t-taire', fmtNum(ta.actual, 0, ' °C'), `MÍN ${fmtNum(ta.min, 0, ' °C')} · MÁX ${fmtNum(ta.max, 0, ' °C')}`);
    setTxt('#t-tsuelo', fmtNum(amb.temperaturaSueloC, 0, ' °C'));
    setTxt('#t-viento', `${fmtNum(vi.velocidadMs, 1, ' m/s')} ${vi.direccion || ''}`.trim(), vi.tipo || '');
    setTxt('#t-rafaga', fmtNum(vi.rafagasMs, 1, ' m/s'), vi.tipo || '');
    setTxt('#t-hr', `${fmtNum(hr.dia)}–${fmtNum(hr.madrugada, 0, ' %')}`, 'Humedad relativa: día – madrugada');
    // Odómetro de la misión (dato real) o, si falta, distancia geodésica recorrida en la ruta
    const odo = Number.isFinite(nav.distanciaAcumuladaMetros) ? nav.distanciaAcumuladaMetros : recorridoHasta(S.idx);
    setTxt('#t-dist', odo >= 1000 ? `${(odo / 1000).toFixed(1)} km` : `${Math.round(odo)} m`,
      Number.isFinite(nav.distanciaTramoMetros) ? `Tramo: ${nav.distanciaTramoMetros} m` : '');
    $('#t-min').innerHTML = (p.minerales || []).map(m =>
      `<span class="min-chip" title="${esc(m.fuente)}"><b>${esc(m.nombre)}</b> ${Math.round(m.confianza * 100)}%</span>`).join('');
  }

  function actualizarAlertas(p) {
    const U = S.U, al = [], nav = p.navegacion || {}, amb = p.ambiente || {};
    if (p.pendiente_grados > U.pendiente_peligro_grados)
      al.push(['crit', `⚠ PENDIENTE CRÍTICA ${p.pendiente_grados.toFixed(1)}° > ${U.pendiente_peligro_grados}° · RIESGO DE DESLIZAMIENTO`]);
    if (nivelTerreno(nav.estadoTerreno) === 'crit') al.push(['crit', `⚠ TERRENO ${nav.estadoTerreno.replace(/^PELIGRO\s*-\s*/i, '').toUpperCase()}`]);
    if (p.oxigeno_pct < U.oxigeno_critico_pct) al.push(['crit', `⚠ O₂ CRÍTICO ${p.oxigeno_pct}% · REGRESO INMEDIATO`]);
    else if (p.oxigeno_pct < U.oxigeno_bajo_pct) al.push(['warn', `O₂ BAJO ${p.oxigeno_pct}% · PLANIFICAR RETORNO`]);
    const fr = p.radiacion_acumulada_msv / U.radiacion_limite_eva_msv;
    if (fr > 0.8) al.push(['crit', `⚠ DOSIS ACUMULADA ${Math.round(fr * 100)}% DEL LÍMITE EVA`]);
    else if (fr > 0.5) al.push(['warn', `DOSIS ACUMULADA ${Math.round(fr * 100)}% DEL LÍMITE EVA`]);
    if (p.pendiente_max_grados > U.pendiente_peligro_grados)
      al.push(['warn', `PENDIENTE MÁX. DEL ENTORNO ${p.pendiente_max_grados.toFixed(1)}° > ${U.pendiente_peligro_grados}°`]);
    const raf = amb.viento?.rafagasMs;
    if (Number.isFinite(raf) && raf >= (U.rafaga_precaucion_ms ?? Infinity))
      al.push(['warn', `RÁFAGAS ${raf.toFixed(1)} m/s · ${(amb.viento.tipo || 'VIENTO').toUpperCase()}`]);
    const sol = amb.radiacion?.alertaSolar;
    if (sol && !/^nominal/i.test(sol)) al.push(['warn', `☀ ${sol.toUpperCase()}`]);
    const zonas = (p.hotspots || []).filter(esPeligro).length;
    if (zonas && !al.length) al.push(['warn', `${zonas} ZONA(S) CON PENDIENTE > ${U.pendiente_peligro_grados}° EN ESTE PUNTO`]);
    al.sort((a, b) => (a[0] === 'crit' ? 0 : 1) - (b[0] === 'crit' ? 0 : 1));

    $('#alerts').innerHTML = al.slice(0, 2).map(([n, t]) => `<div class="alert ${n === 'warn' ? 'warn' : ''}">${esc(t)}</div>`).join('');
    $('#vignette').classList.toggle('crit', al.some(a => a[0] === 'crit'));
  }

  // ---------- Detalle de hotspot ----------
  function mostrarDetalle(h, peligro) {
    const d = $('#detail'), U = S.U;
    let html = '<button class="close" type="button" title="Cerrar (Esc)">✕</button>';
    // Texto: hallazgo (qué se ve) + impacto_humanidad (por qué importa); descripcion como respaldo
    const hall = h.hallazgo || h.descripcion;
    const textos = (hall ? `<div class="d-sec">HALLAZGO</div><p>${esc(hall)}</p>` : '')
      + (h.impacto_humanidad ? `<div class="d-sec">IMPACTO PARA LA HUMANIDAD</div><p class="impacto">${esc(h.impacto_humanidad)}</p>` : '');
    if (h.tipo === 'ciencia') {
      d.className = 'panel brackets sci';
      const conf = numOr(h.confianza, 0);
      html += `<div class="tag">◆ DETECCIÓN · ${esc(h.instrumento || 'CRISM')}</div><h3>${esc(h.titulo)}</h3>
        <div class="kv"><span class="dim">MINERAL</span><b>${esc(h.mineral)}</b></div>
        <div class="kv"><span class="dim">FÓRMULA</span><b>${esc(h.formula)}</b></div>
        ${h.banda_um ? `<div class="kv"><span class="dim">BANDA</span><b>${esc(h.banda_um)}${/^[\d.\s/]+$/.test(h.banda_um) ? ' µm' : ''}</b></div>` : ''}
        <div class="kv"><span class="dim">FUENTE</span><b>${esc(h.fuente)}</b></div>
        <div class="metric ${conf > 0.7 ? 'ok' : conf > 0.5 ? 'warn' : 'crit'}" style="margin-top:10px">
          <div class="m-row"><span class="m-lbl">CONFIANZA</span><b class="m-val">${Math.round(conf * 100)}<small>%</small></b></div>
          <div class="bar"><div class="fill" style="width:${conf * 100}%"></div></div></div>
        ${textos}`;
    } else {
      d.className = 'panel brackets ' + (peligro ? 'danger' : 'caution');
      html += `<div class="tag">${peligro ? '⚠ ALERTA DE PELIGRO · TERRENO' : '▲ EVALUACIÓN DE TERRENO'}</div><h3>${esc(h.titulo)}</h3>
        <div class="kv"><span class="dim">PENDIENTE</span><b>${fmtPend(h)}</b></div>
        <div class="kv"><span class="dim">UMBRAL</span><b>${U.pendiente_peligro_grados}°</b></div>
        <div class="kv"><span class="dim">ESTADO</span><b style="color:${peligro ? 'var(--alert)' : 'var(--caution)'}">${peligro ? 'NO TRANSITABLE' : 'TRANSITABLE CON PRECAUCIÓN'}</b></div>
        ${textos}`;
    }
    d.innerHTML = html;
    d.hidden = false;
    d.querySelector('.close').addEventListener('click', cerrarDetalle);
  }
  function cerrarDetalle() { $('#detail').hidden = true; }

  // =========================================================
  //  MINIMAPA (Leaflet)
  // =========================================================
  function initMapa() {
    const A = S.data.mision.assets, lim = A.mapa_limites;
    S.lim = lim; S.geo = geoRef(lim); S.limB = L.latLngBounds(lim);
    const map = S.map = L.map('minimap', {
      zoomControl: false, attributionControl: false, zoomSnap: 0.25,
      minZoom: 0, maxZoom: 22, keyboard: false, maxBoundsViscosity: 1,
    });
    ajustarMapa();

    // El overlay usa EXACTAMENTE los límites de datos: sin padding ni márgenes.
    // Las imágenes reales son cuadradas (1:1) y mapa_limites es una caja cuadrada en el terreno.
    const real = A.usar_mapa_real && A.mapa;
    const urlBase = real ? A.mapa : generarMapa(lim);
    const ov = (url, o) => L.imageOverlay(url, S.limB, Object.assign({ interactive: false }, o));
    S.capas.base = ov(urlBase).addTo(map);
    MODOS = MODOS_TODOS.filter(m => m.id !== 'hipso' || (real && A.mapa_hipso));
    if (real && A.mapa_hipso) S.capas.hipso = ov(A.mapa_hipso);
    S.capas.pendiente = ov(generarCampo('pendiente', lim), { opacity: 0.85, className: 'ov-field' });
    S.capas.hidratacion = ov(generarCampo('hidratacion', lim), { opacity: 0.9, className: 'ov-field' });

    // Aristas únicas de la ruta
    S.aristas = []; const vistas = new Set();
    S.P.forEach(p => (p.conexiones || []).forEach(id => {
      const k = [p.id, id].sort().join('|');
      if (vistas.has(k) || !porId(id)) return;
      vistas.add(k); S.aristas.push([p, porId(id)]);
    }));
    S.ruta = L.layerGroup().addTo(map);

    // Cono de visión
    S.cono = L.marker([S.P[0].lat, S.P[0].lon], {
      icon: L.divIcon({
        className: 'map-cone', iconSize: [120, 120], iconAnchor: [60, 60],
        html: `<div class="cone-rot"><svg viewBox="-60 -60 120 120" width="120" height="120">
          <defs><radialGradient id="cg" cx="0" cy="0" r="56" gradientUnits="userSpaceOnUse">
          <stop offset="0" stop-color="#00F0FF" stop-opacity=".7"/><stop offset="1" stop-color="#00F0FF" stop-opacity="0"/></radialGradient></defs>
          <path class="cone-path" fill="url(#cg)" stroke="#00F0FF" stroke-opacity=".6" stroke-width="1"/></svg></div><div class="cone-dot"></div>`,
      }),
      interactive: false, keyboard: false, zIndexOffset: 1000,
    }).addTo(map);
    S.coneRot = S.cono.getElement().querySelector('.cone-rot');
    S.conePath = S.cono.getElement().querySelector('.cone-path');

    // Marcadores de puntos
    S.marcadores = S.P.map((p, i) => {
      const peligro = puntoPeligro(p);
      const m = L.marker([p.lat, p.lon], {
        icon: L.divIcon({ className: 'map-pt' + (peligro ? ' danger' : ''), html: `${i + 1}`, iconSize: [20, 20], iconAnchor: [10, 10] }),
        keyboard: false, zIndexOffset: 2000,
      }).addTo(map);
      m.bindTooltip(`${p.id.toUpperCase()} · ${p.nombre}`, { direction: 'top', offset: [0, -10], className: 'map-tip' });
      m.on('click', () => irA(i));
      return m;
    });

    // Control "Modo Capas"
    const Capas = L.Control.extend({
      options: { position: 'bottomleft' },   // abajo, junto a la leyenda: los puntos de Gale se agrupan en la mitad norte
      onAdd() {
        const b = L.DomUtil.create('button', 'layer-btn');
        b.type = 'button'; b.title = 'Modo Capas (L): ' + MODOS.map(m => m.label.toLowerCase()).join(' / ');
        L.DomEvent.disableClickPropagation(b);
        b.addEventListener('click', ciclarCapa);
        S.btnCapa = b; return b;
      },
    });
    map.addControl(new Capas());
    const Leyenda = L.Control.extend({
      options: { position: 'bottomleft' },
      onAdd() { const d = L.DomUtil.create('div', 'legend'); S.leyenda = d; return d; },
    });
    map.addControl(new Leyenda());
    aplicarCapa();
    window.addEventListener('resize', () => { ajustarMapa(); actualizarMapaPunto(S.P[S.idx]); });
  }

  // Zoom mínimo = el que CUBRE todo el contenedor con los límites del mapa (inside=true),
  // y los límites máximos de paneo = los del overlay → nunca se ven franjas vacías.
  function ajustarMapa() {
    const { map, limB } = S;
    map.invalidateSize(false);
    const sz = map.getSize();
    if (!sz.x || !sz.y) return;
    const z = map.getBoundsZoom(limB, true);
    map.setMinZoom(z); map.setMaxZoom(z + 4);
    map.setView(limB.getCenter(), z, { animate: false });
    map.setMaxBounds(limB);
  }

  function ciclarCapa() { S.modo = (S.modo + 1) % MODOS.length; aplicarCapa(); }

  function aplicarCapa() {
    const m = MODOS[S.modo].id, { map, capas } = S;
    ['hipso', 'pendiente', 'hidratacion'].forEach(k => { if (capas[k] && map.hasLayer(capas[k])) map.removeLayer(capas[k]); });
    if (m !== 'satelital' && capas[m]) capas[m].addTo(map);
    capas.base.setOpacity(m === 'satelital' || m === 'hipso' ? 1 : 0.55);
    dibujarRuta();
    S.btnCapa.innerHTML = `<span>MODO ${S.modo + 1}/${MODOS.length} · CAPAS ⟳</span>${MODOS[S.modo].label}`;
    S.leyenda.innerHTML = leyendaHTML(m);
  }

  // Ruta segura opcional: mision.ruta_segura = lista de ids de punto, [lat,lon] o {lat,lon}
  function rutaSegura() {
    const rs = S.data.mision.ruta_segura;
    if (!Array.isArray(rs) || rs.length < 2) return null;
    const pts = rs.map(q => {
      if (typeof q === 'string') { const p = porId(q); return p && [p.lat, p.lon]; }
      if (Array.isArray(q)) return q;
      return q && Number.isFinite(q.lat) ? [q.lat, q.lon] : null;
    }).filter(Boolean);
    return pts.length > 1 ? pts : null;
  }

  function dibujarRuta() {
    const m = MODOS[S.modo].id, U = S.U.pendiente_peligro_grados;
    S.ruta.clearLayers();
    const linea = (ll, col, o = {}) => {
      L.polyline(ll, { color: '#0B0F19', weight: 6, opacity: 0.7, interactive: false }).addTo(S.ruta);
      L.polyline(ll, Object.assign({ color: col, weight: 2.5, interactive: false }, o)).addTo(S.ruta);
    };
    if (m === 'pendiente') {
      // Obstáculos opcionales: mision.obstaculos = [{ lat, lon, radio_m, nombre }]
      (S.data.mision.obstaculos || []).forEach(o => {
        if (!Number.isFinite(o.lat) || !Number.isFinite(o.lon)) return;
        // Leaflet convierte metros con el radio terrestre; se corrige a radio marciano
        const r = (o.radio_m || 30) * 6378137 / S.R;
        const c = L.circle([o.lat, o.lon], { radius: r, color: '#FF3B30', weight: 1.5, fillColor: '#FF3B30', fillOpacity: 0.35, interactive: false }).addTo(S.ruta);
        if (o.nombre) c.bindTooltip(esc(o.nombre), { className: 'map-tip' });
      });
      const seg = rutaSegura();
      if (seg) {
        S.aristas.forEach(([a, b]) => L.polyline([[a.lat, a.lon], [b.lat, b.lon]],
          { color: '#8E8E93', weight: 1.5, dashArray: '2 6', opacity: 0.8, interactive: false }).addTo(S.ruta));
        linea(seg, '#30D158', { weight: 3.5 });
      } else {
        S.aristas.forEach(([a, b]) => {
          const mal = Math.max(a.pendiente_max_grados, b.pendiente_max_grados) > U;
          linea([[a.lat, a.lon], [b.lat, b.lon]], mal ? '#FF3B30' : '#30D158', { dashArray: mal ? '3 5' : null, weight: 3 });
        });
      }
      return;
    }
    S.aristas.forEach(([a, b]) => linea([[a.lat, a.lon], [b.lat, b.lon]], m === 'hidratacion' ? '#E6FFFF' : '#00F0FF', { dashArray: '6 5' }));
  }

  function leyendaHTML(m) {
    const U = S.U.pendiente_peligro_grados, A = S.data.mision.assets;
    if (m === 'satelital') {
      const fuente = A.usar_mapa_real ? `HiRISE ${esc(A.hirise?.producto || '')}`.trim() : 'PLACEHOLDER';
      return `<div>SATÉLITE REAL · ${fuente}</div><div class="lg-lbl"><span style="color:var(--cyan)">— RUTA EVA</span><span style="color:var(--alert)">● PELIGRO</span></div>`;
    }
    if (m === 'hipso') {
      return `<div>MAPA HIPSOMÉTRICO · MOLA</div><div class="lg-bar" style="background:linear-gradient(90deg,#4b2d8f,#3b5bd6,#3fb8c8,#d9c97a,#a0522d)"></div>
        <div class="lg-lbl"><span>BAJO</span><span>ELEVACIÓN</span><span>ALTO</span></div>`;
    }
    if (m === 'pendiente') {
      return `<div>PENDIENTES Y OBSTÁCULOS</div>
        <div class="lg-lbl"><span style="color:var(--alert)">■ &gt;${U}° (NO TRANSITABLE)</span></div>
        <div class="lg-lbl"><span style="color:#30D158">— RUTA SEGURA</span></div>`;
    }
    const R = RAMPAS.hidratacion;
    const grad = R.stops.map(([t, c]) => `rgb(${c.join(',')}) ${t * 100}%`).join(',');
    return `<div>HIDRATACIÓN MINERAL / ISRU · % H₂O</div><div class="lg-bar" style="background:linear-gradient(90deg,rgba(0,0,0,0),${grad})"></div>
      <div class="lg-lbl"><span>${R.min}%</span><span>${Math.round((R.min + R.max) / 2)}%</span><span>${R.max}%</span></div>`;
  }

  function actualizarMapaPunto(p) {
    if (!S.map || !p) return;
    S.cono.setLatLng([p.lat, p.lon]);
    S.marcadores.forEach((m, i) => {
      const el = m.getElement(); if (!el) return;
      el.classList.toggle('active', i === S.idx);
      el.classList.toggle('visited', i < S.idx);
    });
    S.map.panTo([p.lat, p.lon], { animate: true, duration: 0.8 });
  }

  function actualizarCono(heading, hfov) {
    if (!S.coneRot) return;
    S.coneRot.style.transform = `rotate(${heading}deg)`;
    const a = clamp(hfov, 20, 140) / 2 * RAD, r = 56;
    const sx = (r * Math.sin(a)).toFixed(2), sy = (-r * Math.cos(a)).toFixed(2);
    S.conePath.setAttribute('d', `M0 0 L${-sx} ${sy} A${r} ${r} 0 0 1 ${sx} ${sy} Z`);
  }

  // =========================================================
  //  BRÚJULA + BUCLE DE RENDER
  // =========================================================
  function initBrujula() {
    const c = $('#compass');
    const resize = () => {
      const r = c.getBoundingClientRect();
      c.width = Math.max(1, r.width * S.dpr); c.height = Math.max(1, r.height * S.dpr);
      S.heading = -1;
    };
    S.cmp = c; S.cmpCtx = c.getContext('2d');
    resize(); window.addEventListener('resize', resize);
  }

  function dibujarBrujula(h) {
    const c = S.cmp, g = S.cmpCtx, W = c.width, H = c.height, d = S.dpr;
    g.clearRect(0, 0, W, H);
    const ppd = 3.2 * d, span = W / 2 / ppd;
    g.lineWidth = 1 * d; g.textAlign = 'center'; g.font = `600 ${11 * d}px ${FONT}`;
    for (let k = Math.ceil(h - span); k <= h + span; k++) {
      const dn = norm360(k);
      if (dn % 5) continue;
      const x = W / 2 + (k - h) * ppd, big = dn % 45 === 0, mid = dn % 15 === 0;
      g.strokeStyle = g.fillStyle = big ? '#00F0FF' : 'rgba(0,240,255,.6)';
      g.beginPath(); g.moveTo(x, H); g.lineTo(x, H - (big ? 14 : mid ? 9 : 5) * d); g.stroke();
      if (mid) g.fillText(big ? CARD[dn / 45] : String(dn).padStart(3, '0'), x, H - 18 * d);
    }
    // Rumbo hacia los puntos conectados
    const p = S.P[S.idx];
    (p.conexiones || []).forEach(id => {
      const n = porId(id); if (!n) return;
      const dd = norm180(rumbo(p, n) - h);
      if (Math.abs(dd) > span) return;
      const x = W / 2 + dd * ppd;
      g.fillStyle = '#FF9F0A';
      g.beginPath(); g.moveTo(x - 5 * d, 2 * d); g.lineTo(x + 5 * d, 2 * d); g.lineTo(x, 9 * d); g.fill();
      g.font = `700 ${9 * d}px ${FONT}`; g.fillText(id.toUpperCase(), x + 14 * d, 9 * d);
      g.font = `600 ${11 * d}px ${FONT}`;
    });
  }

  function bucle() {
    // Mientras carga una escena, getYaw() aún pertenece a la anterior: no sincronizar
    if (S.viewer && S.viewer.isLoaded()) {
      try {
        const p = S.P[S.idx];
        const heading = norm360(p.rumbo_centro + S.viewer.getYaw());
        const hfov = S.viewer.getHfov();
        if (Math.abs(heading - S.heading) > 0.1 || Math.abs(hfov - S.hfov) > 0.1) {
          S.heading = heading; S.hfov = hfov;
          actualizarCono(heading, hfov);
          dibujarBrujula(heading);
          $('#heading-readout').textContent = `${pad3(heading)}° ${CARD[Math.round(heading / 45) % 8]}`;
        }
      } catch (e) { /* el visor aún está cargando */ }
    }
    requestAnimationFrame(bucle);
  }

  // =========================================================
  //  UI: navegación, teclado, estado
  // =========================================================
  function actualizarNav() {
    const p = S.P[S.idx];
    $('#nav-label').textContent = `${p.id.toUpperCase()} · ${p.nombre}`;
    $('#btn-prev').disabled = S.idx === 0;
    $('#btn-next').disabled = S.idx === S.P.length - 1;
    $('#nav-dots').innerHTML = S.P.map((q, i) =>
      `<i class="${i === S.idx ? 'on' : i < S.idx ? 'done' : ''}" data-i="${i}" title="${esc(q.nombre)}"></i>`).join('');
  }

  function pantallaCompleta() {
    if (!document.fullscreenElement) document.documentElement.requestFullscreen?.().catch(() => { });
    else document.exitFullscreen?.();
  }

  function initUI() {
    initBrujula();
    $('#btn-prev').addEventListener('click', () => irA(S.idx - 1));
    $('#btn-next').addEventListener('click', () => irA(S.idx + 1));
    $('#btn-fs').addEventListener('click', pantallaCompleta);
    $('#nav-dots').addEventListener('click', e => { const i = e.target.dataset.i; if (i != null) irA(+i); });
    window.addEventListener('keydown', e => {
      const k = e.key.toLowerCase();
      if (k === 'q' || k === 'pageup') irA(S.idx - 1);
      else if (k === 'e' || k === 'pagedown') irA(S.idx + 1);
      else if (k === 'l') ciclarCapa();
      else if (k === 'f') pantallaCompleta();
      else if (k === 'escape') cerrarDetalle();
      else if (/^[1-9]$/.test(k)) irA(+k - 1);
    });
  }

  function registrarSW() {
    const el = $('#s-cache');
    if (!('serviceWorker' in navigator)) { el.textContent = 'SW N/D'; el.classList.add('warn'); return; }
    navigator.serviceWorker.register('service-worker.js')
      .then(() => navigator.serviceWorker.ready)
      .then(() => { el.textContent = 'OFFLINE ✓'; el.classList.add('ok'); })
      .catch(err => { el.textContent = 'SW ERROR'; el.classList.add('crit'); console.warn('[Ares-360] SW:', err); });
  }

  function conectividad() {
    const el = $('#s-net');
    const f = () => {
      const on = navigator.onLine;
      el.textContent = on ? 'ENLACE ORBITAL' : 'MODO AUTÓNOMO';
      el.className = 'chip ' + (on ? 'ok' : 'warn');
    };
    f(); window.addEventListener('online', f); window.addEventListener('offline', f);
  }

  // Hora solar media local de Marte (algoritmo Mars24 / Allison & McEwen)
  function relojMarte() {
    const LON_E = 137.44, SOL0_CURIOSITY = 49269;   // Cráter Gale · sol 0 = aterrizaje MSL (6-ago-2012)
    const f = () => {
      const jdTT = Date.now() / 86400000 + 2440587.5 + 69.184 / 86400;
      const msd = (jdTT - 2405522.0028779) / 1.0274912517;
      const lmst = ((msd % 1) * 24 + LON_E / 15) % 24;
      const sol = Math.floor(msd + LON_E / 360) - SOL0_CURIOSITY;
      const hh = Math.floor(lmst), mm = Math.floor((lmst - hh) * 60), ss = Math.floor(((lmst - hh) * 60 - mm) * 60);
      $('#s-sol').textContent = `SOL ${sol}`;
      $('#s-lmst').textContent = `LMST ${[hh, mm, ss].map(v => String(v).padStart(2, '0')).join(':')}`;
    };
    f(); setInterval(f, 1000);
  }

  window.addEventListener('DOMContentLoaded', boot);
})();
