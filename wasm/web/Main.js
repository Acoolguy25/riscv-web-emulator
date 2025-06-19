import App from "./App.js";
import init, { WasmRiscv } from "./simmerv_wasm.js";
import { Terminal } from "xterm";  // Correctly imports Terminal
import { FitAddon } from 'xterm-addon-fit';

/* ---------- constants ---------- */
const SCREENS     = 3;
const ROOTFS_PATH = "./bin/ktfs.raw";
const COLUMNS = 90;
const MINIMUM_ROWS = 32;
let isFullScreen = false;
let onResize;

/* ---------- build terminals ---------- */
const terms = [], panes = [], fits = [];
let terminal;
const screenButtons = document.getElementById("screen-buttons")
const starterButtons = document.getElementsByClassName("controls-bar")[0]
const termContainer = document.getElementById("terminal-container")
const fullScreen = document.getElementById("fullscreen-button")
const divider = document.getElementById("middle-divider")
const infoContent = document.getElementById("tab-content-info")
const imgDiagram = document.getElementById('blockImgDiagram')

for (let i = 0; i < SCREENS; i++) {
    const pane = document.getElementById(`terminal${i}`);
    panes.push(pane);

    const term = new Terminal({   
        cursorBlink: true,         // enable blinking
        convertEol: true,
        cursorStyle: 'block',      // cursor shape: block, bar, underline
        cols: COLUMNS,
        rows: MINIMUM_ROWS,
        theme: {

        },
    });
    const fitAddon = new FitAddon();
    term.loadAddon(fitAddon);
    term.open(pane);
    term.resize(140, 32);

    if (i === 0) {
        term.writeln("This is a RISC-V emulator written in Rust + WASM.");
        term.writeln("Press “Run Games” to boot my shell with games running on all 3 screens.");
        term.writeln("Press “Run Shell” to boot my stand-alone shell.");
        term.writeln("");
        terminal = term
    }
    else{
        term.writeln("To display content asynchronously on this screen, run the following command:")
        term.writeln("$ spawn " + (i + 1) + " <program>")
        pane.style.display = 'none'
    }
    term.write("\x1b[?25l")
    pane.addEventListener('wheel', (e) => {
      const delta = e.deltaY;
      const scrollTop = pane.scrollTop;
      const scrollHeight = pane.scrollHeight;
      const clientHeight = pane.clientHeight;

      if (
        (delta > 0 && scrollTop + clientHeight < scrollHeight) ||  // scrolling down and can scroll more
        (delta < 0 && scrollTop > 0)                               // scrolling up and can scroll more
      ) {
        e.stopPropagation();  // prevent scroll bubbling to page
      }
    });
    terms.push(term);
    fits.push(fitAddon);
}

/* ---------- screen switching ---------- */
function show(idx) {
  if (window.app){
    const old = window.app.setActiveTerminal(idx);
    panes[old].style.display = "none";
    panes[idx].style.display = 'flex';
    panes[idx].setAttribute("tabindex", "0");
    terms[idx].focus()
    terminal = terms[idx]
    onResize();
    
  }
}

document.addEventListener("fullscreenchange", () => {
  if (document.fullscreenElement){
    isFullScreen = true;
  }
  else{
    isFullScreen = false;
    fullScreen.classList.remove("active")
  }
  onResize();
})

document
  .querySelectorAll("#screen-buttons .btn")
  .forEach((btn, idx) => {
    btn.onclick = () => {
      if (btn == fullScreen){ // fullscreen
        if (btn.classList.contains("active")){
          document.exitFullscreen();
          btn.classList.remove("active")
        }
        else{
          termContainer.requestFullscreen().catch(err => {
            console.error(`Error attempting to enable fullscreen: ${err.message}`);
          });
          btn.classList.add("active")
        }
        terminal.focus()
      }
      else{
          document
            .querySelectorAll("#screen-buttons .btn")
            .forEach((b, idx) => {
              if (idx < terms.length){
                b.classList.remove("active")
              }
        });
          btn.classList.add("active");
          show(+btn.dataset.screen);
      }
    };
  });

/* ---------- run controls ---------- */
const runBtn  = document.getElementById("run-button");
const gameBtn = document.getElementById("run-game");
const fileSel = document.getElementById("file-select");
const dbgChk  = document.getElementById("debug-checkbox");

let wasmReady = false;
init().then(() => {
  wasmReady       = true;
  runBtn.disabled = false;
  gameBtn.disabled = false;
});
const rootFS_PATH = fetch(ROOTFS_PATH);
const fileSel_PATH = fetch(fileSel.value);

async function startFunc(inputStr){
  if (!wasmReady) return;
  runBtn.disabled = true
  dbgChk.disabled = true
  gameBtn.disabled = true

  terms[0].clear()
  terms[0].write("\x1b[?25h")
  terms[0].writeln("Loading file system...")
  const fsBuf  = await (await rootFS_PATH).arrayBuffer();
  terms[0].writeln("Loading program...")
  const elfBuf = await (await fileSel_PATH).arrayBuffer();

  const riscv = WasmRiscv.new(inputStr);
  riscv.setup_program(new Uint8Array(elfBuf));
  if (fsBuf.byteLength) riscv.setup_filesystem(new Uint8Array(fsBuf));

  window.app = new App(riscv, terms, {
    debugModeEnabled: dbgChk.checked,
    runCyclesNum:     0x10000,
  });

  screenButtons.className =(`d-flex justify-content-center gap-2 mb-2`)
  screenButtons.style.display = 'block'
  starterButtons.style.display = 'none'
  show(0);
  // if (dbgChk.checked){
  terms[0].clear()
  terms[0].write("\x1b[?25h")
  // }
  dbgChk.checked ? window.app.startDebugMode() : window.app.run();
}
gameBtn.onclick = async () => {
  startFunc("1");
}
runBtn.onclick = async () => {
  startFunc("0");
};

// Boring resizing
// From https://github.com/xtermjs/xterm.js/tree/master/addons/xterm-addon-fit
onResize = () => {
    const screenButtonsBottom = screenButtons.getBoundingClientRect().bottom;
    const availableHeight = window.innerHeight - screenButtonsBottom;
    const fontSize = 17;
    const cellPadding = 0; // a rough estimate, tweak if needed
    const rowHeight = fontSize + cellPadding;

    for (let i = 0; i < terms.length; i++) {
        const term = terms[i];
        const fit = fits[i];

        const dims = fit.proposeDimensions();
        if (!dims) continue;

        if (isFullScreen) {
            const rows = Math.floor(availableHeight / rowHeight);
            term.resize(Math.max(COLUMNS,isNaN(dims.cols)?term.cols:dims.cols),
              Math.max(MINIMUM_ROWS, rows));
        } else {
          term.resize(Math.max(COLUMNS,isNaN(dims.cols)?term.cols:dims.cols),
              MINIMUM_ROWS);       
        }
    }
    divider.style.width = termContainer.offsetWidth + "px"
    infoContent.style.width = Math.max(0, termContainer.offsetWidth) + "px"
    imgDiagram.style.width = termContainer.offsetWidth + "px"
};

window.addEventListener('resize', onResize);
onResize();
